#!/usr/bin/env python3
import socket
import struct
import time
import random
import json
import sys
import argparse
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Tuple, Any, Union
from enum import IntEnum
import hashlib
from collections import defaultdict

class DNSRecordType(IntEnum):
    A = 1
    NS = 2
    CNAME = 5
    SOA = 6
    MX = 15
    TXT = 16
    AAAA = 28
    SRV = 33
    ANY = 255

@dataclass
class DNSRecord:
    name: str
    type: DNSRecordType
    ttl: int
    data: Any
    section: str = "answer"
    preference: Optional[int] = None
    creation_time: float = None
    
    def __post_init__(self):
        if self.creation_time is None:
            self.creation_time = time.time()
    
    @property
    def remaining_ttl(self) -> int:
        elapsed = time.time() - self.creation_time
        remaining = self.ttl - int(elapsed)
        return max(0, remaining)
    
    @property
    def is_expired(self) -> bool:
        return self.remaining_ttl <= 0
    
    def to_cache_dict(self) -> dict:
        result = {
            'name': self.name,
            'type': self.type.name,
            'ttl': self.ttl,
            'remaining_ttl': self.remaining_ttl,
            'original_ttl': self.ttl,
            'section': self.section,
            'creation_time': self.creation_time,
            'is_expired': self.is_expired
        }
        if self.type == DNSRecordType.MX:
            result['preference'] = self.preference
            result['exchange'] = self.data
        elif isinstance(self.data, dict):
            result.update(self.data)
        else:
            result['data'] = str(self.data)
        return result
    
    @classmethod
    def from_cache_dict(cls, data: dict) -> 'DNSRecord':
        record_type = DNSRecordType[data['type']]
        creation_time = data.get('creation_time', time.time())
        
        if record_type == DNSRecordType.MX:
            return cls(
                name=data['name'],
                type=record_type,
                ttl=data['ttl'],
                data=data['exchange'],
                section=data['section'],
                preference=data.get('preference'),
                creation_time=creation_time
            )
        return cls(
            name=data['name'],
            type=record_type,
            ttl=data['ttl'],
            data=data.get('data', ''),
            section=data['section'],
            creation_time=creation_time
        )
    
    def __str__(self):
        type_str = self.type.name
        if self.type == DNSRecordType.MX:
            return f"{type_str}\t{self.preference}\t{self.data}"
        if self.type == DNSRecordType.SOA and isinstance(self.data, dict):
            soa = self.data
            return f"{type_str}\t{soa.get('mname', '')} {soa.get('rname', '')} ({soa.get('serial', 0)} {soa.get('refresh', 0)} {soa.get('retry', 0)} {soa.get('expire', 0)} {soa.get('minimum', 0)})"
        return f"{type_str}\t{self.data}"

class TTLCache:
    def __init__(self, filename: str = None, max_size: int = 1000, default_ttl: int = 300):
        self.filename = filename or "/tmp/dns_ttl_cache.json"
        self.max_size = max_size
        self.default_ttl = default_ttl
        self.data = {}
        self.stats = {'hits': 0, 'misses': 0, 'evictions': 0}
        self._load()
    
    def _key(self, domain: str, qtype: DNSRecordType, server: str = "default") -> str:
        domain_norm = domain.lower().rstrip('.')
        return hashlib.sha256(f"{domain_norm}:{qtype.value}:{server}".encode()).hexdigest()
    
    def _load(self):
        try:
            with open(self.filename, 'r') as f:
                loaded = json.load(f)
                
                if isinstance(loaded, list):
                    self.data = {}
                    for item in loaded:
                        if isinstance(item, dict) and 'key' in item:
                            key = item['key']
                            self.data[key] = {k: v for k, v in item.items() if k != 'key'}
                elif isinstance(loaded, dict):
                    self.data = {k: v for k, v in loaded.items() if not self._is_expired(v)}
                else:
                    self.data = {}
                
                self._cleanup()
        except (FileNotFoundError, json.JSONDecodeError):
            self.data = {}
    
    def _save(self):
        self._cleanup()
        with open(self.filename, 'w') as f:
            json.dump(self.data, f, indent=2)
    
    def _is_expired(self, entry: dict) -> bool:
        expires_at = entry.get('expires_at', 0)
        return time.time() > expires_at
    
    def _cleanup(self):
        initial_count = len(self.data)
        self.data = {k: v for k, v in self.data.items() if not self._is_expired(v)}
        expired_count = initial_count - len(self.data)
        if expired_count > 0:
            self.stats['evictions'] += expired_count
        
        if len(self.data) > self.max_size:
            sorted_items = sorted(self.data.items(), key=lambda x: x[1].get('expires_at', 0))
            self.data = dict(sorted_items[-self.max_size:])
    
    def get(self, domain: str, qtype: DNSRecordType, server: str = "default") -> Optional[List[DNSRecord]]:
        key = self._key(domain, qtype, server)
        
        if key not in self.data:
            self.stats['misses'] += 1
            return None
        
        entry = self.data[key]
        
        if self._is_expired(entry):
            del self.data[key]
            self.stats['misses'] += 1
            self._save()
            return None
        
        self.stats['hits'] += 1
        
        cached_records = []
        for rec_data in entry.get('records', []):
            rec_data['creation_time'] = entry.get('query_time', time.time())
            cached_records.append(DNSRecord.from_cache_dict(rec_data))
        
        return cached_records
    
    def set(self, domain: str, qtype: DNSRecordType, records: List[DNSRecord], 
            server: str = "default", negative: bool = False, query_time: float = None):
        if query_time is None:
            query_time = time.time()
        
        key = self._key(domain, qtype, server)
        
        if negative:
            ttl = min(300, records[0].ttl if records else self.default_ttl)
            cache_records = []
        elif records:
            ttl = min(r.ttl for r in records)
            cache_records = [r.to_cache_dict() for r in records]
        else:
            ttl = self.default_ttl
            cache_records = []
        
        entry = {
            'domain': domain,
            'type': qtype.name,
            'records': cache_records,
            'ttl': ttl,
            'expires_at': query_time + ttl,
            'query_time': query_time,
            'server': server,
            'negative': negative
        }
        
        self.data[key] = entry
        self._save()
    
    def set_negative(self, domain: str, qtype: DNSRecordType, ttl: int = None, 
                    server: str = "default", query_time: float = None):
        if query_time is None:
            query_time = time.time()
        
        key = self._key(domain, qtype, server)
        ttl = ttl or self.default_ttl
        
        entry = {
            'domain': domain,
            'type': qtype.name,
            'records': [],
            'ttl': ttl,
            'expires_at': query_time + ttl,
            'query_time': query_time,
            'server': server,
            'negative': True
        }
        
        self.data[key] = entry
        self._save()
    
    def delete(self, domain: str, qtype: DNSRecordType, server: str = "default"):
        key = self._key(domain, qtype, server)
        if key in self.data:
            del self.data[key]
            self._save()
    
    def clear(self):
        self.data = {}
        try:
            import os
            os.remove(self.filename)
        except:
            pass
    
    def get_stats(self) -> dict:
        self._cleanup()
        total = self.stats['hits'] + self.stats['misses']
        hit_rate = self.stats['hits'] / total if total > 0 else 0
        
        positive = sum(1 for v in self.data.values() if not v.get('negative', False))
        negative = sum(1 for v in self.data.values() if v.get('negative', False))
        
        return {
            'total_entries': len(self.data),
            'positive_entries': positive,
            'negative_entries': negative,
            'cache_hits': self.stats['hits'],
            'cache_misses': self.stats['misses'],
            'evictions': self.stats['evictions'],
            'hit_rate': round(hit_rate, 3)
        }
    
    def get_entries(self) -> List[dict]:
        entries = []
        for key, value in self.data.items():
            entry = value.copy()
            entry['key'] = key
            entry['remaining_ttl'] = max(0, entry['expires_at'] - time.time())
            entries.append(entry)
        return entries

class DNSResolver:
    DEFAULT_SERVERS = [
        ("8.8.8.8", 53),
        ("1.1.1.1", 53),
        ("9.9.9.9", 53)
    ]
    
    def __init__(self, servers=None, timeout=3, retries=2, use_cache=True, cache_file=None):
        self.servers = servers or self.DEFAULT_SERVERS
        self.timeout = timeout
        self.retries = retries
        self.use_cache = use_cache
        self.cache = TTLCache(cache_file) if use_cache else None
        self.query_stats = defaultdict(int)
    
    def build_query(self, domain, qtype):
        tid = random.randint(0, 65535)
        flags = 0x0100
        
        header = struct.pack(">HHHHHH", tid, flags, 1, 0, 0, 0)
        
        qname = b""
        for label in domain.rstrip('.').split('.'):
            qname += struct.pack("B", len(label)) + label.encode('ascii', errors='ignore')
        qname += b"\x00"
        
        question = qname + struct.pack(">HH", qtype, 1)
        
        return header + question, tid
    
    def parse_name(self, data, offset):
        labels = []
        jumped = False
        original_offset = offset
        
        while True:
            if offset >= len(data):
                break
            
            length = data[offset]
            offset += 1
            
            if length == 0:
                break
            
            if length & 0xC0 == 0xC0:
                if offset >= len(data):
                    break
                pointer = struct.unpack(">H", data[offset-1:offset+1])[0] & 0x3FFF
                if not jumped:
                    original_offset = offset + 1
                offset = pointer
                jumped = True
                continue
            
            if offset + length > len(data):
                break
            
            label_bytes = data[offset:offset+length]
            try:
                label = label_bytes.decode('ascii')
            except UnicodeDecodeError:
                try:
                    label = label_bytes.decode('utf-8')
                except UnicodeDecodeError:
                    label = label_bytes.decode('latin-1')
            
            labels.append(label)
            offset += length
        
        return ".".join(labels), original_offset if jumped else offset
    
    def parse_record(self, data, offset, section):
        name, offset = self.parse_name(data, offset)
        
        if offset + 10 > len(data):
            raise ValueError("Record header truncated")
        
        rtype, rclass, ttl, rdlength = struct.unpack(">HHIH", data[offset:offset+10])
        offset += 10
        
        if offset + rdlength > len(data):
            raise ValueError("Record data truncated")
        
        rdata = data[offset:offset+rdlength]
        rdata_offset = offset
        offset += rdlength
        
        parsed_data = self.parse_rdata(rtype, rdata, data, rdata_offset)
        
        if rtype == DNSRecordType.MX and isinstance(parsed_data, tuple):
            exchange, preference = parsed_data
            return DNSRecord(name, DNSRecordType(rtype), ttl, exchange, section, preference), offset
        
        return DNSRecord(name, DNSRecordType(rtype), ttl, parsed_data, section), offset
    
    def parse_rdata(self, rtype, rdata, packet, offset):
        try:
            if rtype == DNSRecordType.A:
                if len(rdata) == 4:
                    return socket.inet_ntop(socket.AF_INET, rdata)
            elif rtype == DNSRecordType.AAAA:
                if len(rdata) == 16:
                    return socket.inet_ntop(socket.AF_INET6, rdata)
            elif rtype == DNSRecordType.MX:
                if len(rdata) >= 2:
                    preference = struct.unpack(">H", rdata[:2])[0]
                    exchange, _ = self.parse_name(packet, offset + 2)
                    return exchange, preference
            elif rtype in (DNSRecordType.CNAME, DNSRecordType.NS):
                return self.parse_name(packet, offset)[0]
            elif rtype == DNSRecordType.TXT:
                result = []
                pos = 0
                while pos < len(rdata):
                    length = rdata[pos]
                    pos += 1
                    if pos + length > len(rdata):
                        break
                    try:
                        txt = rdata[pos:pos+length].decode('utf-8')
                    except UnicodeDecodeError:
                        txt = rdata[pos:pos+length].decode('latin-1')
                    result.append(txt)
                    pos += length
                return "".join(result)
        except Exception:
            pass
        
        return rdata.hex()
    
    def parse_response(self, data, expected_tid, domain, qtype, query_time):
        if len(data) < 12:
            raise ValueError("Response too short")
        
        tid, flags, qdcount, ancount, nscount, arcount = struct.unpack(">HHHHHH", data[:12])
        
        if tid != expected_tid:
            raise ValueError(f"Transaction ID mismatch")
        
        rcode = flags & 0x000F
        if rcode != 0:
            error_names = {0: "NOERROR", 1: "FORMERR", 2: "SERVFAIL", 3: "NXDOMAIN", 4: "NOTIMP", 5: "REFUSED"}
            error_msg = error_names.get(rcode, f"RCODE_{rcode}")
            
            if rcode == 3:
                raise NameError(f"Domain '{domain}' not found")
            raise ValueError(f"DNS server error: {error_msg}")
        
        records = []
        offset = 12
        
        for _ in range(qdcount):
            _, offset = self.parse_name(data, offset)
            offset += 4
        
        for _ in range(ancount):
            try:
                record, offset = self.parse_record(data, offset, "answer")
                records.append(record)
            except ValueError:
                continue
        
        for _ in range(nscount):
            try:
                record, offset = self.parse_record(data, offset, "authority")
                records.append(record)
            except ValueError:
                continue
        
        for _ in range(arcount):
            try:
                record, offset = self.parse_record(data, offset, "additional")
                records.append(record)
            except ValueError:
                continue
        
        return records
    
    def query_server(self, domain, qtype, server, query_time):
        query, tid = self.build_query(domain, qtype)
        ip, port = server
        
        sock = None
        try:
            family = socket.AF_INET6 if ':' in ip and not ip.startswith('[') else socket.AF_INET
            sock = socket.socket(family, socket.SOCK_DGRAM)
            sock.settimeout(self.timeout)
            
            connect_ip = ip.strip('[]') if '[' in ip and ']' in ip else ip
            
            sock.connect((connect_ip, port))
            sock.send(query)
            
            try:
                data, _ = sock.recvfrom(512)
            except socket.timeout:
                self.query_stats[f"timeout_{ip}"] += 1
                raise TimeoutError(f"Timeout after {self.timeout} seconds")
            
            records = self.parse_response(data, tid, domain, qtype, query_time)
            self.query_stats[f"success_{ip}"] += 1
            return records
            
        except socket.timeout:
            self.query_stats[f"timeout_{ip}"] += 1
            raise TimeoutError(f"Timeout connecting to {ip}:{port}")
        except ConnectionRefusedError:
            self.query_stats[f"refused_{ip}"] += 1
            raise ConnectionError(f"Connection refused by {ip}:{port}")
        except OSError as e:
            self.query_stats[f"error_{ip}"] += 1
            raise ConnectionError(f"Network error: {e}")
        except Exception as e:
            self.query_stats[f"error_{ip}"] += 1
            raise
        finally:
            if sock:
                sock.close()
    
    def resolve(self, domain, qtype="A", server=None, follow_cnames=True, depth=0):
        if isinstance(qtype, str):
            try:
                qtype = DNSRecordType[qtype.upper()]
            except KeyError:
                raise ValueError(f"Unknown query type: {qtype}")
        
        domain = domain.rstrip('.')
        query_time = time.time()
        
        if self.use_cache and self.cache:
            cached = self.cache.get(domain, qtype, str(server or "default"))
            if cached:
                valid_records = [r for r in cached if not r.is_expired]
                if valid_records:
                    return valid_records
        
        servers = [server] if server else self.servers
        last_error = None
        
        for attempt in range(self.retries):
            for current_server in servers:
                try:
                    records = self.query_server(domain, qtype, current_server, query_time)
                    
                    if not records:
                        if self.use_cache and self.cache:
                            self.cache.set_negative(domain, qtype, 300, str(current_server), query_time)
                        return []
                    
                    if self.use_cache and self.cache:
                        self.cache.set(domain, qtype, records, str(current_server), False, query_time)
                    
                    if qtype == DNSRecordType.ANY:
                        return records
                    
                    target_records = [r for r in records if r.type == qtype and r.section == "answer"]
                    cname_records = [r for r in records if r.type == DNSRecordType.CNAME and r.section == "answer"]
                    
                    if target_records:
                        return target_records
                    elif follow_cnames and cname_records and depth < 10:
                        cname_target = cname_records[0].data
                        return self.resolve(cname_target, qtype, server, follow_cnames, depth + 1)
                    
                    return []
                    
                except NameError as e:
                    if self.use_cache and self.cache:
                        self.cache.set_negative(domain, qtype, 300, str(current_server), query_time)
                    raise
                except Exception as e:
                    last_error = str(e)
                    if attempt < self.retries - 1:
                        time.sleep(min(2 ** attempt, 4))
        
        raise Exception(f"All attempts failed. Last error: {last_error}")
    
    def get_stats(self):
        stats = {
            'query_stats': dict(self.query_stats),
            'server_count': len(self.servers)
        }
        if self.use_cache and self.cache:
            stats['cache_stats'] = self.cache.get_stats()
        return stats
    
    def clear_cache(self):
        if self.use_cache and self.cache:
            self.cache.clear()

def main():
    parser = argparse.ArgumentParser(description="DNS Resolver with TTL Cache")
    parser.add_argument("domain", nargs="?", help="Domain to query")
    parser.add_argument("-t", "--type", default="A", help="Record type (A, AAAA, MX, etc.)")
    parser.add_argument("-s", "--server", help="DNS server (ip:port)")
    parser.add_argument("--no-cache", action="store_true", help="Disable cache")
    parser.add_argument("--clear-cache", action="store_true", help="Clear cache")
    parser.add_argument("--stats", action="store_true", help="Show cache statistics")
    parser.add_argument("--list-cache", action="store_true", help="List cached entries")
    parser.add_argument("--json", action="store_true", help="JSON output")
    
    args = parser.parse_args()
    
    resolver = DNSResolver(use_cache=not args.no_cache)
    
    if args.clear_cache:
        resolver.clear_cache()
        print("Cache cleared")
        return
    
    if args.stats:
        stats = resolver.get_stats()
        if args.json:
            print(json.dumps(stats, indent=2))
        else:
            print("Resolver Statistics:")
            print(f"  Servers configured: {stats['server_count']}")
            for key, value in stats['query_stats'].items():
                print(f"  {key}: {value}")
            if 'cache_stats' in stats:
                cache_stats = stats['cache_stats']
                print("\nCache Statistics:")
                print(f"  Total entries: {cache_stats['total_entries']}")
                print(f"  Positive entries: {cache_stats['positive_entries']}")
                print(f"  Negative entries: {cache_stats['negative_entries']}")
                print(f"  Cache hits: {cache_stats['cache_hits']}")
                print(f"  Cache misses: {cache_stats['cache_misses']}")
                print(f"  Hit rate: {cache_stats['hit_rate']:.1%}")
        return
    
    if args.list_cache:
        if resolver.use_cache:
            entries = resolver.cache.get_entries()
            if args.json:
                print(json.dumps(entries, indent=2))
            else:
                for entry in entries:
                    print(f"{entry['domain']} ({entry['type']}): "
                          f"TTL={entry['ttl']}, "
                          f"Remaining={entry['remaining_ttl']}, "
                          f"Expires in {entry['remaining_ttl']}s")
        return
    
    if not args.domain:
        parser.print_help()
        return
    
    try:
        server = None
        if args.server:
            parts = args.server.split(":")
            ip = parts[0]
            port = int(parts[1]) if len(parts) > 1 else 53
            server = (ip, port)
        
        records = resolver.resolve(args.domain, args.type, server)
        
        if args.json:
            result = {
                'domain': args.domain,
                'type': args.type,
                'records': [r.to_cache_dict() for r in records],
                'query_time': time.time()
            }
            print(json.dumps(result, indent=2))
        else:
            print(f"\nDNS {args.type} records for {args.domain}:")
            sections = defaultdict(list)
            for r in records:
                sections[r.section].append(r)
            
            for sec in ['answer', 'authority', 'additional']:
                if sections[sec]:
                    print(f"\n;; {sec.capitalize()} Section:")
                    for rec in sections[sec]:
                        print(f"{rec.name}\t{rec.ttl}\tIN\t{rec}")
            print()
            
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
