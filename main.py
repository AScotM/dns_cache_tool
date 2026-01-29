#!/usr/bin/env python3

import socket
import struct
import time
import random
import json
import sys
import argparse
import os
import threading
import tempfile
import ipaddress
from dataclasses import dataclass, asdict, field
from typing import List, Dict, Optional, Tuple, Any, Union, Set
from enum import IntEnum
import hashlib
from collections import defaultdict, OrderedDict
import pathlib
import secrets


class DNSRecordType(IntEnum):
    A = 1
    NS = 2
    CNAME = 5
    SOA = 6
    MX = 15
    TXT = 16
    AAAA = 28
    SRV = 33
    PTR = 12
    DS = 43
    DNSKEY = 48
    RRSIG = 46
    NSEC = 47
    NSEC3 = 50
    TLSA = 52
    ANY = 255


@dataclass
class DNSRecord:
    name: str
    type: DNSRecordType
    ttl: int
    data: Any
    section: str = "answer"
    preference: Optional[int] = None
    creation_time: float = field(default_factory=time.time)
    
    def __post_init__(self):
        if self.creation_time is None:
            self.creation_time = time.time()
    
    @property
    def remaining_ttl(self):
        elapsed = time.time() - self.creation_time
        remaining = self.ttl - int(elapsed)
        return max(0, remaining)
    
    @property
    def is_expired(self):
        return self.remaining_ttl <= 0
    
    def to_cache_dict(self):
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
        elif self.type == DNSRecordType.SOA and isinstance(self.data, dict):
            result.update({'soa_' + k: v for k, v in self.data.items()})
        elif self.type == DNSRecordType.SRV and isinstance(self.data, dict):
            result.update({'srv_' + k: v for k, v in self.data.items()})
        elif isinstance(self.data, dict):
            result.update(self.data)
        else:
            result['data'] = str(self.data)
        
        return result
    
    @classmethod
    def from_cache_dict(cls, data):
        record_type = DNSRecordType[data['type']]
        creation_time = data.get('creation_time', time.time())
        
        if record_type == DNSRecordType.MX:
            return cls(
                name=data['name'],
                type=record_type,
                ttl=data['ttl'],
                data=data.get('exchange', ''),
                section=data.get('section', 'answer'),
                preference=data.get('preference'),
                creation_time=creation_time
            )
        elif record_type == DNSRecordType.SOA:
            soa_data = {}
            for key in ['mname', 'rname', 'serial', 'refresh', 'retry', 'expire', 'minimum']:
                if f'soa_{key}' in data:
                    soa_data[key] = data[f'soa_{key}']
            return cls(
                name=data['name'],
                type=record_type,
                ttl=data['ttl'],
                data=soa_data,
                section=data.get('section', 'answer'),
                creation_time=creation_time
            )
        return cls(
            name=data['name'],
            type=record_type,
            ttl=data['ttl'],
            data=data.get('data', ''),
            section=data.get('section', 'answer'),
            creation_time=creation_time
        )
    
    def __str__(self):
        type_str = self.type.name
        if self.type == DNSRecordType.MX:
            return f"{type_str}\t{self.preference}\t{self.data}"
        elif self.type == DNSRecordType.SOA and isinstance(self.data, dict):
            soa = self.data
            return f"{type_str}\t{soa.get('mname', '')} {soa.get('rname', '')} ({soa.get('serial', 0)} {soa.get('refresh', 0)} {soa.get('retry', 0)} {soa.get('expire', 0)} {soa.get('minimum', 0)})"
        elif self.type == DNSRecordType.SRV and isinstance(self.data, dict):
            srv = self.data
            return f"{type_str}\t{srv.get('priority', 0)} {srv.get('weight', 0)} {srv.get('port', 0)} {srv.get('target', '')}"
        return f"{type_str}\t{self.data}"


class AtomicJSONFile:
    def __init__(self, filename):
        self.filename = pathlib.Path(filename)
        self.lock = threading.RLock()
    
    def load(self):
        with self.lock:
            if not self.filename.exists():
                return {}
            with open(self.filename, 'r') as f:
                return json.load(f)
    
    def save(self, data):
        with self.lock:
            with tempfile.NamedTemporaryFile(
                mode='w',
                dir=str(self.filename.parent),
                prefix=self.filename.stem + '_',
                suffix='.tmp',
                delete=False
            ) as f:
                os.chmod(f.name, 0o600)
                json.dump(data, f, indent=2)
                temp_name = f.name
            
            try:
                os.replace(temp_name, str(self.filename))
            except:
                if os.path.exists(temp_name):
                    os.unlink(temp_name)
                raise


class TTLCache:
    def __init__(self, filename=None, max_size=1000, default_ttl=300, cleanup_interval=60):
        if filename:
            filename = os.path.abspath(filename)
            allowed_dirs = [tempfile.gettempdir(), os.path.expanduser("~/.cache")]
            if not any(filename.startswith(d) for d in allowed_dirs):
                raise ValueError(f"Cache file must be in allowed directory: {allowed_dirs}")
        else:
            filename = "/tmp/dns_ttl_cache.json"
        
        self.filename = pathlib.Path(filename)
        self.filename.parent.mkdir(mode=0o700, exist_ok=True, parents=True)
        self.max_size = max_size
        self.default_ttl = default_ttl
        self.cleanup_interval = cleanup_interval
        self.storage = AtomicJSONFile(self.filename)
        self.lock = threading.RLock()
        self.data = {}
        self.stats = {'hits': 0, 'misses': 0, 'evictions': 0, 'last_cleanup': 0}
        self._load()
    
    def _key(self, domain, qtype, server="default"):
        domain_norm = domain.lower().rstrip('.')
        return f"{domain_norm}:{qtype.value}:{server}"
    
    def _load(self):
        with self.lock:
            try:
                loaded = self.storage.load()
                if isinstance(loaded, dict):
                    self.data = {k: v for k, v in loaded.items() if not self._is_expired(v)}
                else:
                    self.data = {}
                self._periodic_cleanup(force=True)
            except (json.JSONDecodeError, OSError):
                self.data = {}
    
    def _save(self):
        with self.lock:
            self._periodic_cleanup()
            self.storage.save(self.data)
    
    def _is_expired(self, entry):
        expires_at = entry.get('expires_at', 0)
        return time.time() > expires_at
    
    def _periodic_cleanup(self, force=False):
        with self.lock:
            now = time.time()
            if not force and now - self.stats['last_cleanup'] < self.cleanup_interval:
                return
            
            initial_count = len(self.data)
            expired_keys = [k for k, v in self.data.items() if self._is_expired(v)]
            
            for key in expired_keys:
                del self.data[key]
            
            expired_count = len(expired_keys)
            if expired_count > 0:
                self.stats['evictions'] += expired_count
            
            if len(self.data) > self.max_size:
                sorted_items = sorted(self.data.items(), key=lambda x: x[1].get('expires_at', 0))
                self.data = dict(sorted_items[-self.max_size:])
                self.stats['evictions'] += initial_count - len(self.data)
            
            self.stats['last_cleanup'] = now
    
    def get(self, domain, qtype, server="default"):
        with self.lock:
            self._periodic_cleanup()
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
                try:
                    cached_records.append(DNSRecord.from_cache_dict(rec_data))
                except (KeyError, ValueError):
                    continue
            
            return cached_records
    
    def set(self, domain, qtype, records, server="default", negative=False, query_time=None):
        with self.lock:
            if query_time is None:
                query_time = time.time()
            
            key = self._key(domain, qtype, server)
            
            if negative:
                ttl = min(300, records[0].ttl if records else self.default_ttl)
                cache_records = []
            elif records:
                valid_records = [r for r in records if not r.is_expired]
                if not valid_records:
                    return
                ttl = min(r.ttl for r in valid_records)
                cache_records = [r.to_cache_dict() for r in valid_records]
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
                'negative': negative,
                'created': time.time()
            }
            
            self.data[key] = entry
            self._save()
    
    def set_negative(self, domain, qtype, ttl=None, server="default", query_time=None):
        with self.lock:
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
                'negative': True,
                'created': time.time()
            }
            
            self.data[key] = entry
            self._save()
    
    def delete(self, domain, qtype, server="default"):
        with self.lock:
            key = self._key(domain, qtype, server)
            if key in self.data:
                del self.data[key]
                self._save()
    
    def clear(self):
        with self.lock:
            self.data = {}
            self.stats = {'hits': 0, 'misses': 0, 'evictions': 0, 'last_cleanup': 0}
            try:
                self.filename.unlink(missing_ok=True)
            except:
                pass
    
    def get_stats(self):
        with self.lock:
            self._periodic_cleanup(force=True)
            total = self.stats['hits'] + self.stats['misses']
            hit_rate = self.stats['hits'] / total if total > 0 else 0
            
            positive = sum(1 for v in self.data.values() if not v.get('negative', False))
            negative = sum(1 for v in self.data.values() if v.get('negative', False))
            
            now = time.time()
            avg_age = sum(now - v.get('created', now) for v in self.data.values()) / len(self.data) if self.data else 0
            
            return {
                'total_entries': len(self.data),
                'positive_entries': positive,
                'negative_entries': negative,
                'cache_hits': self.stats['hits'],
                'cache_misses': self.stats['misses'],
                'evictions': self.stats['evictions'],
                'hit_rate': round(hit_rate, 3),
                'avg_entry_age': round(avg_age, 1)
            }
    
    def get_entries(self):
        with self.lock:
            self._periodic_cleanup()
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
        ("9.9.9.9", 53),
        ("8.8.4.4", 53)
    ]
    
    def __init__(self, servers=None, timeout=3, retries=2, use_cache=True, cache_file=None):
        self.servers = servers or self.DEFAULT_SERVERS
        self.timeout = timeout
        self.retries = retries
        self.use_cache = use_cache
        self.cache = TTLCache(cache_file) if use_cache else None
        self.query_stats = OrderedDict()
        self.max_query_stats = 1000
        self.cname_chain = set()
    
    def get_address_family(self, ip):
        try:
            socket.inet_pton(socket.AF_INET6, ip)
            return socket.AF_INET6
        except socket.error:
            try:
                socket.inet_pton(socket.AF_INET, ip)
                return socket.AF_INET
            except socket.error:
                raise ValueError(f"Invalid IP address: {ip}")
    
    def build_query(self, domain, qtype, edns=False):
        tid = secrets.randbelow(65536)
        flags = 0x0100
        
        if edns:
            arcount = 1
            additional = b"\x00" + struct.pack(">HHIH", 41, 4096, 0, 0)
        else:
            arcount = 0
            additional = b""
        
        header = struct.pack(">HHHHHH", tid, flags, 1, 0, 0, arcount)
        
        qname = b""
        for label in domain.rstrip('.').split('.'):
            label_bytes = label.encode('ascii', 'ignore')
            qname += struct.pack("B", len(label_bytes)) + label_bytes
        qname += b"\x00"
        
        question = qname + struct.pack(">HH", qtype, 1)
        
        return header + question + additional, tid
    
    def parse_name(self, data, offset, max_depth=10):
        labels = []
        jumped = False
        original_offset = offset
        jump_count = 0
        
        while True:
            if offset >= len(data) or jump_count >= max_depth:
                break
            
            length = data[offset]
            offset += 1
            
            if length == 0:
                break
            
            if length & 0xC0 == 0xC0:
                if offset >= len(data):
                    break
                pointer_bytes = data[offset-1:offset+1]
                if len(pointer_bytes) != 2:
                    break
                pointer = struct.unpack(">H", pointer_bytes)[0] & 0x3FFF
                if pointer >= len(data):
                    break
                
                if not jumped:
                    original_offset = offset + 1
                offset = pointer
                jumped = True
                jump_count += 1
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
                    label = label_bytes.decode('latin-1', 'replace')
            
            labels.append(label)
            offset += length
        
        if not labels:
            return "", original_offset if jumped else offset
        
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
        offset += rdlength
        
        parsed_data = self.parse_rdata(rtype, rdata, data, offset - rdlength)
        
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
            elif rtype in (DNSRecordType.CNAME, DNSRecordType.NS, DNSRecordType.PTR):
                return self.parse_name(packet, offset)[0]
            elif rtype == DNSRecordType.TXT:
                txt_strings = []
                idx = 0
                while idx < len(rdata):
                    length = rdata[idx]
                    idx += 1
                    if idx + length > len(rdata):
                        break
                    try:
                        txt_strings.append(rdata[idx:idx+length].decode('utf-8', 'replace'))
                    except:
                        txt_strings.append(rdata[idx:idx+length].hex())
                    idx += length
                return ' '.join(txt_strings) if txt_strings else ''
            elif rtype == DNSRecordType.SOA:
                mname, offset1 = self.parse_name(packet, offset)
                rname, offset2 = self.parse_name(packet, offset1)
                if offset2 + 20 <= len(packet):
                    serial, refresh, retry, expire, minimum = struct.unpack(">IIIII", packet[offset2:offset2+20])
                    return {
                        'mname': mname,
                        'rname': rname,
                        'serial': serial,
                        'refresh': refresh,
                        'retry': retry,
                        'expire': expire,
                        'minimum': minimum
                    }
            elif rtype == DNSRecordType.SRV:
                if len(rdata) >= 6:
                    priority, weight, port = struct.unpack(">HHH", rdata[:6])
                    target, _ = self.parse_name(packet, offset + 6)
                    return {
                        'priority': priority,
                        'weight': weight,
                        'port': port,
                        'target': target
                    }
        except Exception as e:
            pass
        
        return rdata.hex()
    
    def parse_response(self, data, expected_tid, domain, qtype, query_time):
        if len(data) < 12:
            raise ValueError("Response too short")
        
        tid, flags, qdcount, ancount, nscount, arcount = struct.unpack(">HHHHHH", data[:12])
        
        if tid != expected_tid:
            raise ValueError(f"Transaction ID mismatch: expected {expected_tid}, got {tid}")
        
        rcode = flags & 0x000F
        if rcode != 0:
            error_names = {0: "NOERROR", 1: "FORMERR", 2: "SERVFAIL", 3: "NXDOMAIN", 
                          4: "NOTIMP", 5: "REFUSED", 6: "YXDOMAIN", 7: "YXRRSET", 
                          8: "NXRRSET", 9: "NOTAUTH", 10: "NOTZONE"}
            error_msg = error_names.get(rcode, f"RCODE_{rcode}")
            
            if rcode == 3:
                raise NameError(f"Domain '{domain}' not found (NXDOMAIN)")
            raise ValueError(f"DNS server error: {error_msg}")
        
        offset = 12
        questions = []
        
        for _ in range(qdcount):
            try:
                qname, offset = self.parse_name(data, offset)
                if offset + 4 > len(data):
                    raise ValueError("Question section truncated")
                qtype_val, qclass = struct.unpack(">HH", data[offset:offset+4])
                offset += 4
                questions.append((qname.lower(), qtype_val))
            except (ValueError, IndexError) as e:
                raise ValueError(f"Invalid question section: {e}")
        
        domain_normalized = domain.rstrip('.').lower()
        for qname, qtype_val in questions:
            if qname != domain_normalized:
                raise ValueError(f"Question name mismatch: expected {domain_normalized}, got {qname}")
            if qtype_val != qtype.value:
                raise ValueError(f"Question type mismatch: expected {qtype.value}, got {qtype_val}")
        
        records = []
        
        sections = [
            (ancount, "answer"),
            (nscount, "authority"),
            (arcount, "additional")
        ]
        
        for count, section_name in sections:
            for _ in range(count):
                try:
                    record, offset = self.parse_record(data, offset, section_name)
                    records.append(record)
                except (ValueError, IndexError) as e:
                    break
        
        return records
    
    def _update_stats(self, key):
        if len(self.query_stats) >= self.max_query_stats:
            self.query_stats.popitem(last=False)
        self.query_stats[key] = self.query_stats.get(key, 0) + 1
    
    def query_server(self, domain, qtype, server, query_time, use_tcp=False):
        query, tid = self.build_query(domain, qtype, edns=True)
        ip, port = server
        
        sock = None
        family = self.get_address_family(ip)
        
        try:
            if use_tcp:
                sock = socket.socket(family, socket.SOCK_STREAM)
                sock.settimeout(self.timeout)
                sock.connect((ip, port))
                query_len = struct.pack(">H", len(query))
                sock.sendall(query_len + query)
                
                try:
                    length_data = sock.recv(2)
                    if len(length_data) != 2:
                        raise ValueError("Invalid TCP response length")
                    response_len = struct.unpack(">H", length_data)[0]
                    
                    response = b""
                    while len(response) < response_len:
                        chunk = sock.recv(min(4096, response_len - len(response)))
                        if not chunk:
                            break
                        response += chunk
                    
                    if len(response) != response_len:
                        raise ValueError("Incomplete TCP response")
                except socket.timeout:
                    self._update_stats(f"tcp_timeout_{ip}")
                    raise TimeoutError(f"TCP timeout after {self.timeout} seconds")
            else:
                sock = socket.socket(family, socket.SOCK_DGRAM)
                sock.settimeout(self.timeout)
                sock.sendto(query, (ip, port))
                
                try:
                    data, addr = sock.recvfrom(65535)
                    
                    if addr[0] != ip:
                        raise ValueError(f"Response from unexpected source: {addr[0]}")
                    
                    if len(data) >= 12 and (data[2] & 0x02):
                        return self.query_server(domain, qtype, server, query_time, use_tcp=True)
                    
                    response = data
                except socket.timeout:
                    if not use_tcp:
                        return self.query_server(domain, qtype, server, query_time, use_tcp=True)
                    self._update_stats(f"udp_timeout_{ip}")
                    raise TimeoutError(f"UDP timeout after {self.timeout} seconds")
            
            records = self.parse_response(response, tid, domain, qtype, query_time)
            self._update_stats(f"success_{ip}")
            return records
            
        except socket.timeout:
            self._update_stats(f"timeout_{ip}")
            raise TimeoutError(f"Timeout after {self.timeout} seconds")
        except ConnectionRefusedError:
            self._update_stats(f"refused_{ip}")
            raise ConnectionError(f"Connection refused by {ip}:{port}")
        except OSError as e:
            self._update_stats(f"error_{ip}")
            raise ConnectionError(f"Network error: {e}")
        except Exception as e:
            self._update_stats(f"error_{ip}")
            raise
        finally:
            if sock:
                sock.close()
    
    def resolve(self, domain, qtype="A", server=None, follow_cnames=True, visited=None):
        if visited is None:
            visited = set()
        
        if isinstance(qtype, str):
            try:
                qtype = DNSRecordType[qtype.upper()]
            except KeyError:
                raise ValueError(f"Unknown query type: {qtype}")
        
        domain = domain.rstrip('.').lower()
        query_time = time.time()
        
        if domain in visited:
            raise RecursionError(f"CNAME loop detected: {' -> '.join(visited)} -> {domain}")
        
        visited.add(domain)
        
        try:
            if len(visited) > 10:
                raise RecursionError(f"CNAME chain too deep for {domain}")
            
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
                        elif follow_cnames and cname_records:
                            cname_target = cname_records[0].data
                            return self.resolve(cname_target, qtype, server, follow_cnames, visited)
                        
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
        finally:
            visited.discard(domain)
    
    def reverse_lookup(self, ip):
        if not ip or not isinstance(ip, str):
            raise ValueError("IP address must be a non-empty string")
        
        ip = ip.strip()
        try:
            addr_obj = ipaddress.ip_address(ip)
        except ValueError as e:
            raise ValueError(f"Invalid IP address '{ip}': {e}")
        
        if addr_obj.version == 4:
            octets = str(addr_obj).split('.')
            arpa = '.'.join(reversed(octets)) + '.in-addr.arpa'
        else:
            hex_str = addr_obj.exploded.replace(':', '')
            arpa = '.'.join(reversed(hex_str)) + '.ip6.arpa'
        
        return self.resolve(arpa, "PTR")
    
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


def load_config(config_file=None):
    default_config = {
        'servers': [
            {"ip": "8.8.8.8", "port": 53},
            {"ip": "1.1.1.1", "port": 53}
        ],
        'timeout': 3,
        'retries': 2,
        'cache_size': 1000,
        'cache_ttl': 300
    }
    
    if config_file and os.path.exists(config_file):
        try:
            with open(config_file, 'r') as f:
                user_config = json.load(f)
                default_config.update(user_config)
        except:
            pass
    
    servers = [(s['ip'], s.get('port', 53)) for s in default_config['servers']]
    return default_config, servers


def main():
    parser = argparse.ArgumentParser(description="DNS Resolver with TTL Cache")
    parser.add_argument("query", nargs="?", help="Domain to query or IP for reverse lookup")
    parser.add_argument("-t", "--type", default="A", help="Record type (A, AAAA, MX, PTR, etc.)")
    parser.add_argument("-s", "--server", help="DNS server (ip:port)")
    parser.add_argument("--no-cache", action="store_true", help="Disable cache")
    parser.add_argument("--clear-cache", action="store_true", help="Clear cache")
    parser.add_argument("--stats", action="store_true", help="Show cache statistics")
    parser.add_argument("--list-cache", action="store_true", help="List cached entries")
    parser.add_argument("--json", action="store_true", help="JSON output")
    parser.add_argument("--config", help="Configuration file")
    parser.add_argument("--reverse", "-r", action="store_true", help="Reverse DNS lookup")
    parser.add_argument("--debug", action="store_true", help="Debug mode")
    
    args = parser.parse_args()
    
    config, default_servers = load_config(args.config)
    
    resolver = DNSResolver(
        servers=default_servers,
        timeout=config['timeout'],
        retries=config['retries'],
        use_cache=not args.no_cache
    )
    
    if args.clear_cache:
        resolver.clear_cache()
        print("Cache cleared" + (" (JSON)" if args.json else ""))
        return
    
    if args.stats:
        stats = resolver.get_stats()
        if args.json:
            print(json.dumps(stats, indent=2))
        else:
            print("Resolver Statistics:")
            print(f"  Servers configured: {stats['server_count']}")
            for key, value in sorted(stats['query_stats'].items()):
                print(f"  {key}: {value}")
            if 'cache_stats' in stats:
                cache_stats = stats['cache_stats']
                print("\nCache Statistics:")
                print(f"  Total entries: {cache_stats['total_entries']}")
                print(f"  Positive entries: {cache_stats['positive_entries']}")
                print(f"  Negative entries: {cache_stats['negative_entries']}")
                print(f"  Cache hits: {cache_stats['cache_hits']}")
                print(f"  Cache misses: {cache_stats['cache_misses']}")
                print(f"  Evictions: {cache_stats['evictions']}")
                print(f"  Hit rate: {cache_stats['hit_rate']:.1%}")
                print(f"  Avg entry age: {cache_stats['avg_entry_age']:.1f}s")
        return
    
    if args.list_cache:
        if resolver.use_cache:
            entries = resolver.cache.get_entries()
            if args.json:
                print(json.dumps(entries, indent=2))
            else:
                for entry in entries:
                    status = "NEGATIVE" if entry.get('negative') else "POSITIVE"
                    print(f"{entry['domain']:40} {entry['type']:6} {status:8} "
                          f"TTL={entry['ttl']:4} Remaining={entry['remaining_ttl']:4}s")
        return
    
    if not args.query:
        parser.print_help()
        return
    
    try:
        server = None
        if args.server:
            parts = args.server.split(":")
            ip = parts[0]
            port = int(parts[1]) if len(parts) > 1 else 53
            server = (ip, port)
        
        if args.reverse:
            records = resolver.reverse_lookup(args.query)
            qtype = "PTR"
        else:
            records = resolver.resolve(args.query, args.type, server)
            qtype = args.type
        
        if args.json:
            result = {
                'query': args.query,
                'type': qtype,
                'reverse': args.reverse,
                'timestamp': time.time(),
                'records': [r.to_cache_dict() for r in records]
            }
            print(json.dumps(result, indent=2))
        else:
            if args.reverse:
                print(f"\nReverse DNS lookup for {args.query}:")
            else:
                print(f"\nDNS {qtype} records for {args.query}:")
            
            if not records:
                print("No records found")
                return
            
            sections = {}
            for r in records:
                sections.setdefault(r.section, []).append(r)
            
            for sec in ['answer', 'authority', 'additional']:
                if sec in sections and sections[sec]:
                    print(f"\n;; {sec.capitalize()} Section:")
                    for rec in sections[sec]:
                        ttl_str = f"{rec.remaining_ttl}/{rec.ttl}" if rec.ttl > 0 else str(rec.ttl)
                        print(f"{rec.name:40} {ttl_str:>8} IN {rec}")
            print()
            
    except RecursionError as e:
        print(f"Recursion error: {e}", file=sys.stderr)
        sys.exit(2)
    except Exception as e:
        if args.debug:
            import traceback
            traceback.print_exc()
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
