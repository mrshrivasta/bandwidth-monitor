#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
================================================================================
 ARPCHECK
 ARP Entry Validator - CLI + Web App
--------------------------------------------------------------------------------
 Author  : Karanam Shrivasta
 GitHub  : https://github.com/mrshrivasta
 LinkedIn: https://www.linkedin.com/in/karanam-shrivasta/
 Version : 1.0.0
--------------------------------------------------------------------------------
 WHAT THIS ASKS
   Not "has the ARP table changed" - that is a different question, and one this
   machine's other tools already answer. This asks two things about the table as
   it stands right now:

     IS EACH ENTRY INTERNALLY CONSISTENT?
       An address outside the interface's own subnet cannot be reached by ARP at
       all. A broadcast or multicast address in a unicast entry is meaningless. A
       single hardware address claiming several IP addresses is either a router
       doing proxy ARP, or somebody answering for addresses that are not theirs.
       None of that needs the network - it is arithmetic on the table itself.

     IS EACH ENTRY STILL TRUE?
       An ARP entry is a cached claim, and nothing revalidates it until it ages
       out. The active check asks each address again and compares the answer to
       what is cached. A different answer means the cache is stale or wrong; TWO
       answers to one question means two machines are claiming one address, which
       is what ARP spoofing looks like from here.

 *** ARP HAS NO AUTHENTICATION, AND THAT IS THE WHOLE PROBLEM ***
   Any machine can answer for any address, and the last answer wins. There is no
   signature, no challenge, nothing to verify against. So this tool cannot tell
   you which reply is the real one - only that more than one exists, or that what
   is cached no longer matches what the wire says. Deciding which is legitimate
   needs knowledge of your own network. Approve what you recognise.

 A DUPLICATE IS USUALLY NOT AN ATTACK
   One hardware address holding several IP addresses is completely normal for a
   router doing proxy ARP, for a firewall with secondary addresses, and for a
   virtualisation host. What makes it interesting is when it appears where you
   did not expect it, and especially when the address it now covers is the
   GATEWAY - because that is the address worth stealing.

 THE ACTIVE CHECK TRANSMITS
   It broadcasts ARP requests. That is ordinary traffic - every machine does it
   constantly - but it puts this machine's address in front of everything on the
   segment, and it will populate other machines' caches. It always asks first.

 WHAT IT CANNOT SEE
   Only this machine's cache and this machine's segment. ARP does not cross a
   router, so an entry for anything beyond the gateway does not exist here at
   all. And the cache only holds what this machine has recently talked to - a
   device that has never been contacted is simply absent, which is not the same
   as not being there.

 LEGAL DISCLAIMER
   Run it on networks you are responsible for. Provided "as is" with no warranty;
   the author accepts no liability for any loss or damage.
================================================================================
"""

from __future__ import annotations

import argparse
import binascii
import csv
import fcntl
import hashlib
import html as _html
import io
import ipaddress
import json
import math
import os
import platform
import random
import re
import select
import shutil
import socket
import sqlite3
import struct
import sys
import textwrap
import time
from datetime import datetime, timezone

APP_NAME = "ARPCheck"
APP_SHORT = "ARPCHECK"
VERSION = "1.0.0"
AUTHOR = "Karanam Shrivasta"
GITHUB = "https://github.com/mrshrivasta"
LINKEDIN = "https://www.linkedin.com/in/karanam-shrivasta/"
DEFAULT_DB = os.environ.get("ARPCHECK_DB", "arpcheck.db")

NO_AUTHENTICATION = (
    "ARP has no authentication. Any machine can answer for any address and the last answer "
    "wins - there is no signature and nothing to verify against. This tool cannot tell you "
    "which reply is the real one, only that more than one exists or that the cache no longer "
    "matches the wire. Which is legitimate needs knowledge of your own network."
)
DUPLICATE_IS_NORMAL = (
    "One hardware address holding several IP addresses is normal for a router doing proxy "
    "ARP, a firewall with secondary addresses, or a virtualisation host. It matters when it "
    "appears where you did not expect it - and most of all when it covers the gateway."
)
CACHE_LIMIT = (
    "This sees only this machine's cache and this machine's segment. ARP does not cross a "
    "router, and the cache only holds what this machine has recently talked to. A device that "
    "is absent here is not necessarily absent from the network."
)
DISCLAIMER_SHORT = (
    "Validates ARP entries for internal consistency, and optionally re-asks the network to "
    "see whether they are still true. ARP has no authentication, so it cannot tell you which "
    "answer is legitimate - only that something disagrees."
)
DISCLAIMER_LONG = textwrap.dedent(
    """\
    ARP HAS NO AUTHENTICATION. Any machine can answer for any address, and the last answer
    wins. There is no signature and nothing to verify against, so this tool cannot tell you
    which reply is the real one - only that more than one exists, or that what is cached no
    longer matches what the wire says. Deciding which is legitimate needs knowledge of your
    own network.

    A DUPLICATE IS USUALLY NOT AN ATTACK. One hardware address holding several IP addresses
    is completely normal for a router doing proxy ARP, a firewall with secondary addresses,
    or a virtualisation host. What makes it interesting is where it appears - and above all
    whether it covers the gateway, because that is the address worth stealing.

    THE ACTIVE CHECK TRANSMITS. It broadcasts ARP requests. That is ordinary traffic, but it
    puts this machine's address in front of everything on the segment and will populate other
    machines' caches. It is never run without asking.

    IT SEES ONLY THIS MACHINE'S CACHE AND THIS MACHINE'S SEGMENT. ARP does not cross a router,
    so nothing beyond the gateway appears here at all. The cache holds only what this machine
    has recently talked to - an absent device is not necessarily an absent device.

    READ-ONLY BY DEFAULT. It never adds, deletes or alters an ARP entry, and there is no
    command here that does.

    Run it on networks you are responsible for. Provided "as is" with no warranty; the author
    accepts no liability for any loss or damage."""
)

SEVERITIES = ["critical", "high", "medium", "low", "info"]
SEV_WEIGHT = {"critical": 40.0, "high": 20.0, "medium": 8.0, "low": 3.0, "info": 0.0}
SEV_COLOR = {"critical": "#e5484d", "high": "#f76808", "medium": "#ffb224",
             "low": "#3e9dd8", "info": "#8b8f9b"}
STATE_COLOR = {"valid": "#30a46c", "stale": "#ffb224", "conflict": "#e5484d",
               "incomplete": "#8b8f9b", "unverified": "#3e9dd8"}


def risk_band(score: float) -> tuple[str, str]:
    if score >= 40:
        return "investigate now", "#e5484d"
    if score >= 20:
        return "worth investigating", "#f76808"
    if score >= 8:
        return "worth a look", "#ffb224"
    if score > 0:
        return "minor notes", "#3e9dd8"
    return "nothing inconsistent", "#30a46c"


# =============================================================================
# SECTION 1 - Utilities
# =============================================================================

def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def ts_pretty(iso: str | None) -> str:
    if not iso:
        return "-"
    try:
        return datetime.fromisoformat(iso).strftime("%Y-%m-%d %H:%M:%S")
    except Exception:
        return iso


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def html_escape(s) -> str:
    return _html.escape("" if s is None else str(s), quote=True)


def shorten(s, n=90) -> str:
    s = " ".join(str(s or "").split())
    return s if len(s) <= n else s[:n - 1] + "\u2026"


def fmt_duration(seconds) -> str:
    if seconds is None:
        return "-"
    seconds = int(seconds)
    d, r = divmod(seconds, 86400)
    h, r = divmod(r, 3600)
    m, s = divmod(r, 60)
    if d:
        return f"{d}d {h}h"
    if h:
        return f"{h}h {m}m"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


def ago(iso: str | None) -> str:
    if not iso:
        return "never"
    try:
        delta = (datetime.now(timezone.utc) - datetime.fromisoformat(iso)).total_seconds()
    except Exception:
        return "-"
    return fmt_duration(delta) + " ago" if delta >= 0 else "in the future"


def is_root() -> bool:
    try:
        return os.geteuid() == 0
    except AttributeError:
        return False


def F(category, title, severity, description, evidence="", advice=""):
    return {"category": category, "title": title, "severity": severity,
            "description": description, "evidence": str(evidence)[:2500],
            "advice": advice}


class Result:
    def __init__(self, name: str):
        self.name = name
        self.data = None
        self.status = "ok"
        self.detail = ""

    def unavailable(self, detail):
        self.status, self.detail = "unavailable", detail
        return self

    def partial(self, detail):
        self.status = "partial"
        self.detail = " ".join((self.detail + "; " + detail).strip("; ").split())[:400]
        return self


# =============================================================================
# SECTION 2 - Hardware addresses
# =============================================================================

MAC_RE = re.compile(r"^([0-9a-f]{2}:){5}[0-9a-f]{2}$", re.I)
NULL_MAC = "00:00:00:00:00:00"
BROADCAST_MAC = "ff:ff:ff:ff:ff:ff"

VIRTUAL_OUIS = {
    "000c29": "VMware", "005056": "VMware", "000569": "VMware",
    "080027": "VirtualBox", "0a0027": "VirtualBox",
    "525400": "QEMU/KVM", "00163e": "Xen", "001c42": "Parallels",
    "00155d": "Hyper-V", "0242ac": "Docker", "024200": "Docker",
}
KNOWN_OUIS = {
    "b827eb": "Raspberry Pi", "dca632": "Raspberry Pi", "e45f01": "Raspberry Pi",
    "001e52": "Apple", "3c0754": "Apple", "88665a": "Apple", "ac87a3": "Apple",
    "f0189e": "Apple", "001a2b": "Cisco", "00000c": "Cisco", "0007eb": "Cisco",
    "24a43c": "Ubiquiti", "788a20": "Ubiquiti", "fcecda": "Ubiquiti",
    "000fb5": "NETGEAR", "20e52a": "NETGEAR", "0019cb": "TP-Link",
    "50c7bf": "TP-Link", "a42bb0": "TP-Link", "c46e1f": "TP-Link",
    "001966": "ASUSTek", "2c56dc": "ASUSTek", "00219b": "Dell", "b8ac6f": "Dell",
    "001b78": "HP", "3464a9": "HP", "e0accb": "Lenovo", "001eab": "Samsung",
    "00d0b7": "Intel", "0026c7": "Intel", "8c705a": "Intel", "a088b4": "Intel",
    "00e04c": "Realtek", "001132": "Synology", "0090a9": "Western Digital",
    **VIRTUAL_OUIS,
}


def normalise_mac(mac) -> str:
    m = str(mac or "").strip().lower().replace("-", ":")
    m = re.sub(r"[^0-9a-f:]", "", m)
    parts = [p for p in m.split(":") if p]
    if len(parts) == 6:
        return ":".join(p.zfill(2) for p in parts)
    hexonly = m.replace(":", "")
    if len(hexonly) == 12:
        return ":".join(hexonly[i:i + 2] for i in range(0, 12, 2))
    return m


def describe_mac(mac: str) -> dict:
    m = normalise_mac(mac)
    out = {"mac": m, "valid": bool(MAC_RE.match(m)), "null": m == NULL_MAC,
           "broadcast": m == BROADCAST_MAC, "multicast": False,
           "locally_administered": False, "oui": m.replace(":", "")[:6],
           "vendor": None, "virtual": False}
    if not out["valid"]:
        return out
    first = int(m.split(":")[0], 16)
    out["multicast"] = bool(first & 0x01)
    out["locally_administered"] = bool(first & 0x02)
    out["vendor"] = KNOWN_OUIS.get(out["oui"])
    out["virtual"] = out["oui"] in VIRTUAL_OUIS
    return out


# =============================================================================
# SECTION 3 - Reading the ARP cache and the interfaces it must agree with
# =============================================================================

# /proc/net/arp flags (linux/if_arp.h)
ATF_COM = 0x02          # the entry is complete - a reply was received
ATF_PERM = 0x04         # static: configured by hand, never ages out
ATF_PUBL = 0x08         # published: this machine answers ARP for it (proxy ARP)

ARP_HW_TYPES = {1: "Ethernet", 6: "IEEE 802", 15: "Frame Relay", 16: "ATM",
                17: "HDLC", 18: "Fibre Channel", 32: "InfiniBand", 772: "loopback"}

SIOCGIFADDR = 0x8915
SIOCGIFNETMASK = 0x891B


def interface_networks() -> dict:
    """Each interface's own address and subnet - what an ARP entry must fall in."""
    out: dict[str, dict] = {}
    base = "/sys/class/net"
    if not os.path.isdir(base):
        return out
    for name in sorted(os.listdir(base)):
        entry = {"name": name, "address": None, "netmask": None, "network": None,
                 "mac": None, "error": None}
        try:
            with open(os.path.join(base, name, "address")) as fh:
                entry["mac"] = normalise_mac(fh.read().strip())
        except OSError:
            pass
        sock = None
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            packed = struct.pack("256s", name.encode()[:15])
            entry["address"] = socket.inet_ntoa(
                fcntl.ioctl(sock.fileno(), SIOCGIFADDR, packed)[20:24])
            entry["netmask"] = socket.inet_ntoa(
                fcntl.ioctl(sock.fileno(), SIOCGIFNETMASK, packed)[20:24])
            entry["network"] = str(ipaddress.ip_network(
                f"{entry['address']}/{entry['netmask']}", strict=False))
        except OSError as e:
            entry["error"] = f"no IPv4 address configured ({e.strerror or e})"
        except ValueError as e:
            entry["error"] = str(e)
        finally:
            if sock is not None:
                sock.close()
        out[name] = entry
    return out


def default_gateway() -> dict:
    out = {"ip": None, "interface": None, "error": None}
    try:
        with open("/proc/net/route") as fh:
            next(fh, None)
            for raw in fh:
                f = raw.split()
                if len(f) >= 3 and f[1] == "00000000":
                    out["ip"] = socket.inet_ntoa(struct.pack("<I", int(f[2], 16)))
                    out["interface"] = f[0]
                    return out
        out["error"] = "no default route is configured"
    except OSError as e:
        out["error"] = f"could not read the routing table: {e}"
    return out


def read_arp_table() -> Result:
    """The cache as the kernel holds it, with the flags decoded."""
    r = Result("arp")
    r.data = {"entries": [], "source": "/proc/net/arp"}
    path = "/proc/net/arp"
    if not os.path.exists(path):
        return _read_arp_fallback(r)
    try:
        with open(path) as fh:
            next(fh, None)
            for raw in fh:
                f = raw.split()
                if len(f) < 6:
                    continue
                ip, hw_type, flags, mac, mask, device = f[0], f[1], f[2], f[3], f[4], f[5]
                try:
                    flag_int = int(flags, 16)
                    hw_int = int(hw_type, 16)
                except ValueError:
                    continue
                desc = describe_mac(mac)
                r.data["entries"].append({
                    "ip": ip, "mac": desc["mac"], "device": device,
                    "flags": flag_int, "flags_hex": flags,
                    "complete": bool(flag_int & ATF_COM),
                    "permanent": bool(flag_int & ATF_PERM),
                    "published": bool(flag_int & ATF_PUBL),
                    "hw_type": hw_int,
                    "hw_type_name": ARP_HW_TYPES.get(hw_int, f"type {hw_int}"),
                    "mask": mask,
                    "vendor": desc["vendor"], "virtual": desc["virtual"],
                    "locally_administered": desc["locally_administered"],
                    "multicast_mac": desc["multicast"],
                    "broadcast_mac": desc["broadcast"], "null_mac": desc["null"],
                    "valid_mac": desc["valid"],
                })
    except OSError as e:
        return r.unavailable(f"{path} could not be read: {e}")
    if not r.data["entries"]:
        r.partial("the ARP cache is empty - this machine has not recently talked to "
                  "anything on its segment, which is not the same as nothing being there")
    return r


def _read_arp_fallback(r: Result) -> Result:
    """Other platforms have no /proc, so fall back to the 'arp' command and say so."""
    import subprocess
    try:
        proc = subprocess.run(["arp", "-an"], capture_output=True, text=True, timeout=10)
    except FileNotFoundError:
        return r.unavailable(
            f"/proc/net/arp is Linux-only and the 'arp' command was not found, so the "
            f"cache could not be read on {sys.platform}. Nothing below was checked.")
    except Exception as e:
        return r.unavailable(f"the 'arp' command failed: {e}")
    if proc.returncode != 0:
        return r.unavailable(f"the 'arp' command failed: {proc.stderr.strip()[:200]}")
    r.data["source"] = "the 'arp' command"
    for raw in proc.stdout.splitlines():
        m = re.search(r"\(([\d.]+)\)\s+at\s+([0-9a-fA-F:]{11,17})", raw)
        if not m:
            continue
        desc = describe_mac(m.group(2))
        dev = re.search(r"on\s+(\S+)", raw)
        r.data["entries"].append({
            "ip": m.group(1), "mac": desc["mac"],
            "device": dev.group(1) if dev else "?",
            "flags": ATF_COM, "flags_hex": "0x2", "complete": True,
            "permanent": "permanent" in raw.lower(),
            "published": "published" in raw.lower(),
            "hw_type": 1, "hw_type_name": "Ethernet", "mask": "*",
            "vendor": desc["vendor"], "virtual": desc["virtual"],
            "locally_administered": desc["locally_administered"],
            "multicast_mac": desc["multicast"], "broadcast_mac": desc["broadcast"],
            "null_mac": desc["null"], "valid_mac": desc["valid"],
        })
    r.partial("read via the 'arp' command rather than /proc, so the flag detail is coarser "
              "- static and published entries may not be distinguishable")
    return r


# =============================================================================
# SECTION 4 - Validating an entry against itself
#   None of this touches the network. It is arithmetic on the table, the
#   interface addresses and the routing table - which means it works with no
#   privileges and cannot be fooled by anything on the wire.
# =============================================================================

def validate_entry(entry: dict, interfaces: dict, gateway: dict) -> list[dict]:
    """Everything wrong with one entry, considered on its own."""
    problems = []
    ip, mac, dev = entry["ip"], entry["mac"], entry["device"]

    if not entry["valid_mac"]:
        problems.append({"kind": "invalid_mac", "severity": "medium",
                         "detail": f"'{mac}' is not a valid hardware address",
                         "why": "The entry cannot be used as written."})
    if entry["null_mac"] and entry["complete"]:
        problems.append({"kind": "null_mac", "severity": "medium",
                         "detail": "the entry is marked complete but has no hardware "
                                   "address",
                         "why": "Complete means a reply was received, so an all-zeroes "
                                "address contradicts that. On an INCOMPLETE entry this is "
                                "simply what incomplete means and is not reported."})
    if entry["broadcast_mac"]:
        problems.append({"kind": "broadcast_mac", "severity": "high",
                         "detail": "the hardware address is the broadcast address",
                         "why": "No single machine holds the broadcast address, so this "
                                "entry directs unicast traffic to every device on the "
                                "segment. It is malformed, and it is also a way to make "
                                "traffic visible to everyone."})
    elif entry["multicast_mac"]:
        problems.append({"kind": "multicast_mac", "severity": "high",
                         "detail": "the hardware address has the multicast bit set",
                         "why": "A unicast ARP entry should never point at a multicast "
                                "address. Traffic sent to it goes to a group rather than "
                                "to one machine."})

    try:
        addr = ipaddress.ip_address(ip)
    except ValueError:
        problems.append({"kind": "invalid_ip", "severity": "medium",
                         "detail": f"'{ip}' is not a valid address",
                         "why": "The entry is malformed."})
        return problems

    iface = interfaces.get(dev)
    if iface and iface.get("network"):
        try:
            net = ipaddress.ip_network(iface["network"])
            if addr not in net:
                problems.append({
                    "kind": "off_subnet", "severity": "high",
                    "detail": f"{ip} is outside {dev}'s subnet ({iface['network']})",
                    "why": "ARP only works within a subnet, so an address outside it "
                           "cannot legitimately be resolved on this interface. It usually "
                           "means the interface was renumbered and the cache has not caught "
                           "up - and it is also what an entry planted for an address that "
                           "does not belong here looks like."})
            if addr == ipaddress.ip_address(iface["address"] or "0.0.0.0"):
                problems.append({
                    "kind": "own_address", "severity": "medium",
                    "detail": f"{ip} is this machine's own address on {dev}",
                    "why": "A machine does not need an ARP entry for itself. Something "
                           "else answering for your own address is the shape of an "
                           "impersonation attempt."})
        except ValueError:
            pass
    elif iface and iface.get("error"):
        problems.append({"kind": "no_iface_address", "severity": "low",
                         "detail": f"{dev} has no IPv4 address, so the subnet could not be "
                                   f"checked",
                         "why": iface["error"]})
    elif not iface:
        problems.append({"kind": "unknown_device", "severity": "medium",
                         "detail": f"the entry names interface '{dev}', which does not "
                                   f"exist on this machine",
                         "why": "The interface may have been removed since the entry was "
                                "cached."})

    if addr.is_multicast:
        problems.append({"kind": "multicast_ip", "severity": "medium",
                         "detail": f"{ip} is a multicast address",
                         "why": "Multicast addresses map to hardware addresses by formula "
                                "and are never resolved by ARP."})
    if addr.is_loopback:
        problems.append({"kind": "loopback_ip", "severity": "medium",
                         "detail": f"{ip} is a loopback address",
                         "why": "Loopback traffic never reaches the wire, so it has no "
                                "business in an ARP cache."})

    if not entry["complete"] and not entry["permanent"]:
        problems.append({"kind": "incomplete", "severity": "info",
                         "detail": "the entry is incomplete - no reply was received",
                         "why": "The request went out and nothing answered. Ordinary for an "
                                "address that is not in use, and expected while a lookup is "
                                "still in flight."})
    if entry["permanent"]:
        problems.append({"kind": "static", "severity": "info",
                         "detail": "the entry is static and will never age out",
                         "why": "Configured by hand. That is a legitimate defence against "
                                "spoofing, and it also means a wrong entry stays wrong "
                                "until somebody removes it."})
    if entry["published"]:
        problems.append({"kind": "published", "severity": "medium",
                         "detail": "this machine answers ARP for that address (proxy ARP)",
                         "why": "Deliberate on a router or a bridge. On an ordinary host it "
                                "means this machine is answering for an address that is not "
                                "its own, which is worth confirming you configured."})

    if gateway.get("ip") and ip == gateway["ip"]:
        problems.append({"kind": "is_gateway", "severity": "info",
                         "detail": "this is the default gateway",
                         "why": "The single most important entry in the table: everything "
                                "leaving the subnet is sent to this hardware address."})
    return problems


def validate_table(entries: list[dict], interfaces: dict, gateway: dict) -> dict:
    """Cross-entry checks: the things only visible when the table is taken as a whole."""
    out = {"per_entry": {}, "duplicate_macs": [], "duplicate_ips": [],
           "gateway_entry": None, "gateway_shared_with": []}
    for e in entries:
        out["per_entry"][e["ip"]] = validate_entry(e, interfaces, gateway)

    by_mac: dict[str, list] = {}
    by_ip: dict[str, list] = {}
    for e in entries:
        if e["valid_mac"] and not e["null_mac"] and e["complete"]:
            by_mac.setdefault(e["mac"], []).append(e)
        by_ip.setdefault(e["ip"], []).append(e)

    for mac, group in by_mac.items():
        if len(group) > 1:
            out["duplicate_macs"].append({
                "mac": mac, "ips": [g["ip"] for g in group],
                "devices": sorted({g["device"] for g in group}),
                "vendor": group[0].get("vendor"),
                "count": len(group)})
    for ip, group in by_ip.items():
        macs = {g["mac"] for g in group}
        if len(macs) > 1:
            out["duplicate_ips"].append({"ip": ip, "macs": sorted(macs),
                                         "count": len(macs)})

    if gateway.get("ip"):
        for e in entries:
            if e["ip"] == gateway["ip"]:
                out["gateway_entry"] = e
                break
        if out["gateway_entry"]:
            gw_mac = out["gateway_entry"]["mac"]
            out["gateway_shared_with"] = [e["ip"] for e in entries
                                          if e["mac"] == gw_mac
                                          and e["ip"] != gateway["ip"]]
    return out


# =============================================================================
# SECTION 5 - Asking the network whether an entry is still true
#   A cached entry is a claim nobody rechecks until it ages out. This re-asks and
#   compares. It TRANSMITS, so nothing calls it without an explicit confirmation.
# =============================================================================

ETH_P_ARP = 0x0806
ARP_REQUEST, ARP_REPLY = 1, 2


def build_arp_request(src_mac: str, src_ip: str, target_ip: str) -> bytes:
    """An ordinary who-has broadcast, built by hand."""
    src_mac_raw = bytes(int(x, 16) for x in src_mac.split(":"))
    frame = (b"\xff" * 6 + src_mac_raw + struct.pack("!H", ETH_P_ARP))
    frame += struct.pack("!HHBBH", 1, 0x0800, 6, 4, ARP_REQUEST)
    frame += src_mac_raw + socket.inet_aton(src_ip)
    frame += b"\x00" * 6 + socket.inet_aton(target_ip)
    return frame.ljust(60, b"\x00")


def parse_arp_frame(frame: bytes) -> dict | None:
    if len(frame) < 42:
        return None
    if struct.unpack("!H", frame[12:14])[0] != ETH_P_ARP:
        return None
    try:
        htype, ptype, hlen, plen, op = struct.unpack("!HHBBH", frame[14:22])
    except struct.error:
        return None
    if hlen != 6 or plen != 4:
        return None
    sender_mac = ":".join(f"{b:02x}" for b in frame[22:28])
    sender_ip = socket.inet_ntoa(frame[28:32])
    target_mac = ":".join(f"{b:02x}" for b in frame[32:38])
    target_ip = socket.inet_ntoa(frame[38:42])
    return {"op": op, "op_name": {1: "request", 2: "reply"}.get(op, str(op)),
            "sender_mac": sender_mac, "sender_ip": sender_ip,
            "target_mac": target_mac, "target_ip": target_ip,
            "eth_src": ":".join(f"{b:02x}" for b in frame[6:12]),
            "htype": htype, "ptype": ptype}


def verify_entries(entries: list[dict], interfaces: dict, timeout: float = 2.0,
                   per_target_wait: float = 0.6, only_ips: list[str] | None = None,
                   progress=None) -> Result:
    """Re-ask for each address and collect EVERY reply.

    Collecting more than one reply is the point. A single reply that differs from
    the cache means the cache is stale; two replies to one question means two
    machines are claiming one address, which is what spoofing looks like.
    """
    r = Result("verify")
    r.data = {"results": {}, "transmitted": True, "sent": 0, "replies": 0,
              "started": now_iso()}
    if not sys.platform.startswith("linux"):
        return r.unavailable(f"active verification uses AF_PACKET, which is Linux-only; "
                             f"this is {sys.platform}. Nothing was verified.")
    targets = [e for e in entries
               if e["complete"] and e["valid_mac"] and not e["null_mac"]
               and (not only_ips or e["ip"] in only_ips)]
    if not targets:
        return r.unavailable("no complete entries to verify")

    by_device: dict[str, list] = {}
    for e in targets:
        by_device.setdefault(e["device"], []).append(e)

    for device, group in by_device.items():
        iface = interfaces.get(device) or {}
        src_mac, src_ip = iface.get("mac"), iface.get("address")
        if not src_mac or not src_ip:
            r.partial(f"{device} has no usable address, so its {len(group)} entry(ies) "
                      f"were not verified")
            continue
        sock = None
        try:
            sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW,
                                 socket.htons(ETH_P_ARP))
            sock.bind((device, 0))
            sock.settimeout(0.2)
        except PermissionError:
            if sock:
                sock.close()
            return r.unavailable(
                "sending ARP requests needs root. Nothing was verified - which is not the "
                "same as everything being verified and found correct. The consistency "
                "checks above needed no privileges and did run.")
        except OSError as e:
            if sock:
                sock.close()
            r.partial(f"a raw socket on {device} could not be opened: {e}")
            continue
        try:
            for entry in group:
                if progress:
                    progress(entry["ip"])
                replies: list[dict] = []
                try:
                    sock.send(build_arp_request(src_mac, src_ip, entry["ip"]))
                    r.data["sent"] += 1
                except OSError as e:
                    r.partial(f"a request for {entry['ip']} could not be sent: {e}")
                    continue
                deadline = time.time() + per_target_wait
                while time.time() < deadline:
                    try:
                        frame = sock.recv(2048)
                    except socket.timeout:
                        continue
                    except OSError:
                        break
                    msg = parse_arp_frame(frame)
                    if not msg or msg["op"] != ARP_REPLY:
                        continue
                    if msg["sender_ip"] != entry["ip"]:
                        continue
                    if not any(x["sender_mac"] == msg["sender_mac"] for x in replies):
                        replies.append(msg)
                        r.data["replies"] += 1
                r.data["results"][entry["ip"]] = _classify_verification(entry, replies)
        finally:
            try:
                sock.close()
            except Exception:
                pass
    r.data["ended"] = now_iso()
    return r


def _classify_verification(entry: dict, replies: list[dict]) -> dict:
    """What the replies say about the cached entry."""
    macs = [x["sender_mac"] for x in replies]
    out = {"ip": entry["ip"], "cached_mac": entry["mac"], "replies": replies,
           "reply_macs": macs, "state": "unverified", "detail": ""}
    if not replies:
        out["state"] = "silent"
        out["detail"] = ("nothing answered. The device may be off, asleep, or filtering - "
                         "silence does not mean the cached entry is wrong, and it does not "
                         "mean it is right either")
        return out
    if len(set(macs)) > 1:
        out["state"] = "conflict"
        out["detail"] = (f"{len(set(macs))} different machines answered for one address. "
                         f"That is two devices claiming the same address - either a real "
                         f"duplicate, or one of them is lying")
        return out
    if macs[0] == entry["mac"]:
        out["state"] = "valid"
        out["detail"] = "the reply matches what is cached"
    else:
        out["state"] = "stale"
        out["detail"] = (f"the cache says {entry['mac']} and the wire says {macs[0]} - the "
                         f"entry is out of date, or something has taken over the address")
    # a mismatch between the ethernet source and the ARP sender is worth naming
    for x in replies:
        if x["eth_src"] != x["sender_mac"]:
            out["frame_mismatch"] = True
            out["detail"] += (f". The frame came from {x['eth_src']} while the ARP payload "
                              f"claims {x['sender_mac']}, which a well-behaved host does "
                              f"not do")
    return out


# =============================================================================
# SECTION 6 - Findings
# =============================================================================

def analyse(arp: Result, validation: dict, verify: Result | None, interfaces: dict,
            gateway: dict, baseline: dict) -> list[dict]:
    out: list[dict] = []
    if arp.status == "unavailable":
        return [F("Table", "The ARP cache could not be read", "info", arp.detail, "",
                  "Nothing below was checked.")]
    entries = arp.data["entries"]
    approved = {k for k, v in baseline.items() if v.get("approved")}

    if not entries:
        out.append(F("Table", "The ARP cache is empty", "info",
                     "This machine has no cached hardware addresses.", "",
                     CACHE_LIMIT + " An empty cache is normal on a machine that has just "
                     "started or has no local traffic - and it is not the same as nothing "
                     "being there, because the cache only holds what has been talked to."))
        return out

    # ---- the gateway, which is the entry that matters most ----
    gw_entry = validation.get("gateway_entry")
    if gateway.get("ip") and not gw_entry:
        out.append(F("Gateway", f"The gateway {gateway['ip']} is not in the cache", "low",
                     "There is a default route but no ARP entry for it.",
                     f"gateway {gateway['ip']} via {gateway.get('interface')}",
                     "Normal if nothing has left the subnet recently - the entry ages out. "
                     "It simply means there is nothing to validate."))
    elif gw_entry:
        shared = validation.get("gateway_shared_with") or []
        key = f"{gw_entry['ip']}|{gw_entry['mac']}"
        if shared and key not in approved:
            out.append(F("Gateway", f"The gateway's hardware address also covers "
                         f"{len(shared)} other address(es)", "critical",
                         f"{gw_entry['mac']} is cached for the gateway {gw_entry['ip']} and "
                         f"for {', '.join(shared[:6])}.",
                         f"gateway  {gw_entry['ip']} -> {gw_entry['mac']}\n"
                         + "\n".join(f"also     {ip} -> {gw_entry['mac']}"
                                     for ip in shared[:8]),
                         "This is what ARP spoofing looks like: one machine has answered "
                         "for the gateway and for other hosts, so traffic to all of them "
                         "goes to it. It is ALSO exactly what a router doing proxy ARP "
                         "looks like, and what a single box acting as both gateway and "
                         "server looks like. Confirm what that hardware address really is "
                         "before concluding - and if it is your router, approve it."))
        else:
            out.append(F("Gateway", f"The gateway is {gw_entry['ip']} at "
                         f"{gw_entry['mac']}", "info",
                         "Everything leaving this subnet is sent to that hardware address.",
                         f"vendor: {gw_entry.get('vendor') or 'not in this tool\u2019s table'}"
                         f"\ndevice: {gw_entry['device']}"
                         + ("\nstatic entry" if gw_entry["permanent"] else ""),
                         "The single most valuable entry to get right. A static entry here "
                         "is a cheap and effective defence against spoofing."))

    # ---- one hardware address holding several addresses ----
    for dup in validation["duplicate_macs"]:
        if gw_entry and dup["mac"] == gw_entry["mac"]:
            continue                    # already covered, and more sharply, above
        key = f"mac|{dup['mac']}"
        if key in approved:
            continue
        sev = "medium" if dup["count"] <= 3 else "high"
        out.append(F("Duplicates", f"{dup['mac']} is cached for {dup['count']} addresses",
                     sev,
                     "One hardware address is answering for several IP addresses.",
                     f"vendor: {dup.get('vendor') or 'unknown'}\n"
                     + "\n".join(f"  {ip}" for ip in dup["ips"][:10]),
                     DUPLICATE_IS_NORMAL + " Approve it if it is your router."))

    # ---- one address with several hardware addresses ----
    for dup in validation["duplicate_ips"]:
        out.append(F("Duplicates", f"{dup['ip']} appears with {dup['count']} different "
                     f"hardware addresses", "high",
                     "The same address is cached against more than one machine, usually on "
                     "different interfaces.",
                     "\n".join(f"  {mac}" for mac in dup["macs"]),
                     "Two devices configured with one address does this, and so does a "
                     "machine reachable on two segments. It also happens while an address "
                     "is being taken over."))

    # ---- per-entry problems, grouped so one bad table does not produce 200 findings ----
    by_kind: dict[str, list] = {}
    for ip, problems in validation["per_entry"].items():
        for p in problems:
            if p["severity"] == "info":
                continue
            by_kind.setdefault(p["kind"], []).append((ip, p))
    kind_titles = {
        "off_subnet": "outside the interface's subnet",
        "broadcast_mac": "the broadcast hardware address",
        "multicast_mac": "a multicast hardware address",
        "invalid_mac": "an invalid hardware address",
        "invalid_ip": "an invalid IP address",
        "multicast_ip": "a multicast IP address",
        "loopback_ip": "a loopback IP address",
        "own_address": "this machine's own address",
        "unknown_device": "an interface that no longer exists",
        "published": "proxy ARP published by this machine",
        "no_iface_address": "an interface with no address to check against",
        "null_mac": "no hardware address",
    }
    for kind, items in by_kind.items():
        sev = items[0][1]["severity"]
        out.append(F("Entries", f"{len(items)} entry(ies) with {kind_titles.get(kind, kind)}",
                     sev,
                     items[0][1]["detail"] if len(items) == 1
                     else f"{len(items)} entries share this problem.",
                     "\n".join(f"  {ip}: {p['detail']}" for ip, p in items[:8]),
                     items[0][1]["why"]))

    # ---- the shape of the table ----
    complete = [e for e in entries if e["complete"]]
    incomplete = [e for e in entries if not e["complete"] and not e["permanent"]]
    static = [e for e in entries if e["permanent"]]
    if incomplete:
        out.append(F("Table", f"{len(incomplete)} incomplete entry(ies)", "info",
                     "A request went out and nothing answered.",
                     "\n".join(f"  {e['ip']} on {e['device']}" for e in incomplete[:8]),
                     "Ordinary for addresses that are not in use. A large number of them at "
                     "once can mean something is scanning the subnet from this machine."))
    if len(incomplete) > 20:
        out.append(F("Table", f"{len(incomplete)} incomplete entries is a lot", "medium",
                     "Many addresses have been asked for and none answered.",
                     f"{len(incomplete)} incomplete of {len(entries)} total",
                     "This is the trace a subnet sweep leaves in the cache of the machine "
                     "doing the sweeping. If you did not run a scan, something on this "
                     "machine did."))
    if static:
        out.append(F("Table", f"{len(static)} static entry(ies)", "info",
                     "These were configured by hand and never age out.",
                     "\n".join(f"  {e['ip']} -> {e['mac']}" for e in static[:8]),
                     "A good defence for the gateway. It also means a wrong entry stays "
                     "wrong until somebody removes it."))

    la = [e for e in complete
          if e["locally_administered"] and not e["virtual"] and not e["null_mac"]]
    if la:
        out.append(F("Context", f"{len(la)} entry(ies) have a locally-administered address",
                     "info",
                     "The address was assigned by software rather than a manufacturer.",
                     "\n".join(f"  {e['ip']} -> {e['mac']}" for e in la[:8]),
                     "Reported as context only. Virtual machines, containers and phone "
                     "privacy randomisation all set that bit legitimately - it is not "
                     "evidence of anything on its own."))

    # ---- what the wire said ----
    if verify is None:
        out.append(F("Verification", "Entries were NOT verified against the network",
                     "info",
                     "Only the consistency checks ran - nothing was re-asked.", "",
                     "The consistency checks need no privileges and cannot be fooled by "
                     "anything on the wire, but they cannot tell you whether an entry is "
                     "still TRUE. Use 'verify' for that; it transmits, so it asks first."))
    elif verify.status == "unavailable":
        out.append(F("Verification", "Verification did not run", "info", verify.detail, "",
                     "An empty verification result means 'not checked', not 'all correct'."))
    else:
        results = verify.data["results"]
        conflicts = [v for v in results.values() if v["state"] == "conflict"]
        stale = [v for v in results.values() if v["state"] == "stale"]
        silent = [v for v in results.values() if v["state"] == "silent"]
        valid = [v for v in results.values() if v["state"] == "valid"]
        for v in conflicts:
            is_gw = gateway.get("ip") == v["ip"]
            out.append(F("Verification", f"{v['ip']} was claimed by "
                         f"{len(set(v['reply_macs']))} machines"
                         + (" - and it is the GATEWAY" if is_gw else ""),
                         "critical",
                         v["detail"],
                         f"cached: {v['cached_mac']}\n"
                         + "\n".join(f"replied: {m}" for m in dict.fromkeys(v["reply_macs"])),
                         "Two machines answering one address is the clearest signal this "
                         "tool produces. ARP has no authentication, so it cannot tell you "
                         "which is real - but on a healthy network only one should answer. "
                         + ("Traffic leaving this subnet is at stake." if is_gw else "")))
        for v in stale[:8]:
            out.append(F("Verification", f"{v['ip']} does not match what is cached", "high",
                         v["detail"],
                         f"cached:  {v['cached_mac']}\nreplied: {v['reply_macs'][0]}",
                         "A device that was replaced or renumbered produces this and the "
                         "cache simply has not caught up. So does something taking over the "
                         "address. The cache will correct itself; whether it should have "
                         "needed to is the question."))
        for v in results.values():
            if v.get("frame_mismatch"):
                out.append(F("Verification", f"{v['ip']} replied with mismatched addresses",
                             "high",
                             "The ethernet header and the ARP payload name different "
                             "senders.",
                             v["detail"],
                             "A normal host puts the same address in both. A mismatch means "
                             "the reply was crafted rather than generated by a standard "
                             "stack."))
        if valid:
            out.append(F("Verification", f"{len(valid)} entry(ies) confirmed correct",
                         "info",
                         "The wire agrees with the cache for these.",
                         "\n".join(f"  {v['ip']} -> {v['cached_mac']}" for v in valid[:10]),
                         "Confirmed at this moment only. ARP entries can be overwritten at "
                         "any time by anything on the segment."))
        if silent:
            out.append(F("Verification", f"{len(silent)} entry(ies) did not answer", "low",
                         "Nothing replied when these were re-asked.",
                         "\n".join(f"  {v['ip']} (cached as {v['cached_mac']})"
                                   for v in silent[:8]),
                         "The device may be off, asleep or filtering. Silence does not mean "
                         "the cached entry is wrong - and it does not mean it is right."))

    out.append(F("Summary", f"{len(entries)} entry(ies): {len(complete)} complete, "
                 f"{len(incomplete)} incomplete, {len(static)} static", "info",
                 f"from {arp.data['source']}"
                 + (f", verified {len((verify.data or {}).get('results', {}))}"
                    if verify and verify.status == "ok" else ""),
                 "interfaces: " + ", ".join(f"{k} {v['network']}"
                                            for k, v in interfaces.items()
                                            if v.get("network")),
                 NO_AUTHENTICATION))
    return out


def risk_score(findings: list[dict]) -> float:
    return round(clamp(sum(SEV_WEIGHT[f["severity"]] for f in findings), 0, 100), 1)


# =============================================================================
# SECTION 7 - Database
# =============================================================================

SCHEMA = """
CREATE TABLE IF NOT EXISTS scans (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ts TEXT NOT NULL, hostname TEXT, source TEXT, verified INTEGER DEFAULT 0,
    entries INTEGER DEFAULT 0, complete INTEGER DEFAULT 0, incomplete INTEGER DEFAULT 0,
    static INTEGER DEFAULT 0, duplicate_macs INTEGER DEFAULT 0,
    duplicate_ips INTEGER DEFAULT 0, conflicts INTEGER DEFAULT 0,
    stale INTEGER DEFAULT 0, gateway_ip TEXT, gateway_mac TEXT,
    score REAL DEFAULT 0, band TEXT, status TEXT, detail TEXT,
    elapsed_ms INTEGER, payload TEXT,
    critical INTEGER DEFAULT 0, high INTEGER DEFAULT 0, medium INTEGER DEFAULT 0,
    low INTEGER DEFAULT 0, info INTEGER DEFAULT 0, note TEXT
);
CREATE TABLE IF NOT EXISTS observations (
    id INTEGER PRIMARY KEY AUTOINCREMENT, scan_id INTEGER NOT NULL,
    ip TEXT, mac TEXT, device TEXT, complete INTEGER, permanent INTEGER,
    published INTEGER, vendor TEXT, problems TEXT, verify_state TEXT,
    verify_detail TEXT, reply_macs TEXT,
    FOREIGN KEY (scan_id) REFERENCES scans(id)
);
CREATE TABLE IF NOT EXISTS pairs (
    key TEXT PRIMARY KEY, ip TEXT, mac TEXT, first_seen TEXT, last_seen TEXT,
    times_seen INTEGER DEFAULT 0, approved INTEGER DEFAULT 0, approved_at TEXT,
    label TEXT, note TEXT
);
CREATE TABLE IF NOT EXISTS findings (
    id INTEGER PRIMARY KEY AUTOINCREMENT, scan_id INTEGER NOT NULL,
    category TEXT, title TEXT, severity TEXT, description TEXT, evidence TEXT,
    advice TEXT, FOREIGN KEY (scan_id) REFERENCES scans(id)
);
CREATE TABLE IF NOT EXISTS audit_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ts TEXT NOT NULL, level TEXT NOT NULL, source TEXT, message TEXT, scan_id INTEGER
);
CREATE INDEX IF NOT EXISTS idx_obs_scan ON observations(scan_id);
CREATE INDEX IF NOT EXISTS idx_find_scan ON findings(scan_id);
CREATE INDEX IF NOT EXISTS idx_audit_ts ON audit_log(ts);
"""

_DB_PATH = DEFAULT_DB


def set_db_path(p: str) -> None:
    global _DB_PATH
    _DB_PATH = p


def db_path() -> str:
    return _DB_PATH


def connect(path: str | None = None) -> sqlite3.Connection:
    conn = sqlite3.connect(path or _DB_PATH, timeout=30.0)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA busy_timeout=30000")
    conn.execute("PRAGMA foreign_keys=ON")
    return conn


def init_db(conn=None) -> None:
    own = conn is None
    conn = conn or connect()
    try:
        conn.executescript(SCHEMA)
        conn.commit()
    finally:
        if own:
            conn.close()


def q(sql: str, args: tuple = (), conn=None) -> list[sqlite3.Row]:
    own = conn is None
    conn = conn or connect()
    try:
        return conn.execute(sql, args).fetchall()
    finally:
        if own:
            conn.close()


def q1(sql: str, args: tuple = (), conn=None):
    rows = q(sql, args, conn)
    return rows[0] if rows else None


def log_event(level: str, source: str, message: str, scan_id=None, conn=None) -> None:
    own = conn is None
    conn = conn or connect()
    try:
        conn.execute("INSERT INTO audit_log (ts, level, source, message, scan_id) "
                     "VALUES (?,?,?,?,?)",
                     (now_iso(), level.upper(), source,
                      " ".join(str(message).split())[:1000], scan_id))
        conn.commit()
    except Exception:
        pass
    finally:
        if own:
            conn.close()


def baseline_map(conn=None) -> dict:
    out = {}
    for r in q("SELECT * FROM pairs", (), conn):
        d = dict(r)
        d["approved"] = bool(d["approved"])
        out[d["key"]] = d
    return out


def approve_pair(key_or_ip: str, label: str = "", note: str = "") -> tuple[bool, str]:
    conn = connect()
    try:
        init_db(conn)
        row = q1("SELECT * FROM pairs WHERE key=?", (key_or_ip,), conn)
        if not row:
            matches = q("SELECT * FROM pairs WHERE ip=? OR mac=? OR key LIKE ?",
                        (key_or_ip, normalise_mac(key_or_ip), f"%{key_or_ip}%"), conn)
            if len(matches) > 1:
                return False, (f"'{key_or_ip}' matches {len(matches)} pairs. Use the full "
                               f"key: " + ", ".join(m["key"] for m in matches[:3]))
            if not matches:
                return False, (f"'{key_or_ip}' has not been seen. Run a check first, so "
                               f"there is something to approve.")
            row = matches[0]
        conn.execute("UPDATE pairs SET approved=1, approved_at=?, "
                     "label=COALESCE(NULLIF(?,''), label), "
                     "note=COALESCE(NULLIF(?,''), note) WHERE key=?",
                     (now_iso(), label, note, row["key"]))
        conn.commit()
        log_event("INFO", "baseline", f"Approved {row['key']}", None, conn)
        return True, row["key"]
    finally:
        conn.close()


def revoke_pair(key_or_ip: str) -> int:
    conn = connect()
    try:
        n = conn.execute("UPDATE pairs SET approved=0, approved_at=NULL "
                         "WHERE key=? OR ip=? OR mac=?",
                         (key_or_ip, key_or_ip, normalise_mac(key_or_ip))).rowcount
        conn.commit()
        return n
    finally:
        conn.close()


def latest_scan_id(conn=None):
    row = q1("SELECT id FROM scans ORDER BY id DESC LIMIT 1", (), conn)
    return row["id"] if row else None


def scan_summary(sid: int, conn=None):
    row = q1("SELECT * FROM scans WHERE id=?", (sid,), conn)
    if not row:
        return None
    d = dict(row)
    try:
        d["payload"] = json.loads(d["payload"] or "{}")
    except json.JSONDecodeError:
        d["payload"] = {}
    d["band_colour"] = risk_band(d["score"] or 0)[1]
    return d


def save_scan(arp: Result, validation: dict, verify: Result | None,
              findings: list[dict], interfaces: dict, gateway: dict,
              elapsed_ms: int, note: str = "") -> int:
    conn = connect()
    try:
        init_db(conn)
        entries = (arp.data or {}).get("entries", [])
        counts = {s: sum(1 for f in findings if f["severity"] == s) for s in SEVERITIES}
        vres = (verify.data or {}).get("results", {}) if verify else {}
        gw_entry = validation.get("gateway_entry") or {}
        score = risk_score(findings)
        cur = conn.execute(
            "INSERT INTO scans (ts, hostname, source, verified, entries, complete,"
            " incomplete, static, duplicate_macs, duplicate_ips, conflicts, stale,"
            " gateway_ip, gateway_mac, score, band, status, detail, elapsed_ms, payload,"
            " critical, high, medium, low, info, note)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (now_iso(), socket.gethostname(), (arp.data or {}).get("source"),
             int(bool(verify and verify.status == "ok")), len(entries),
             sum(1 for e in entries if e["complete"]),
             sum(1 for e in entries if not e["complete"] and not e["permanent"]),
             sum(1 for e in entries if e["permanent"]),
             len(validation.get("duplicate_macs", [])),
             len(validation.get("duplicate_ips", [])),
             sum(1 for v in vres.values() if v["state"] == "conflict"),
             sum(1 for v in vres.values() if v["state"] == "stale"),
             gateway.get("ip"), gw_entry.get("mac"), score, risk_band(score)[0],
             arp.status, arp.detail, elapsed_ms,
             json.dumps({"entries": entries, "validation": {
                 k: v for k, v in validation.items() if k != "per_entry"},
                 "per_entry": validation.get("per_entry", {}),
                 "verify": vres, "interfaces": interfaces, "gateway": gateway},
                 default=str),
             counts["critical"], counts["high"], counts["medium"], counts["low"],
             counts["info"], note))
        sid = cur.lastrowid
        ts = now_iso()
        for e in entries:
            v = vres.get(e["ip"]) or {}
            probs = validation.get("per_entry", {}).get(e["ip"], [])
            conn.execute(
                "INSERT INTO observations (scan_id, ip, mac, device, complete, permanent,"
                " published, vendor, problems, verify_state, verify_detail, reply_macs)"
                " VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                (sid, e["ip"], e["mac"], e["device"], int(e["complete"]),
                 int(e["permanent"]), int(e["published"]), e.get("vendor"),
                 json.dumps([p["kind"] for p in probs]), v.get("state"),
                 v.get("detail"), json.dumps(v.get("reply_macs", []))))
            if e["complete"] and e["valid_mac"] and not e["null_mac"]:
                key = f"{e['ip']}|{e['mac']}"
                conn.execute(
                    "INSERT INTO pairs (key, ip, mac, first_seen, last_seen, times_seen) "
                    "VALUES (?,?,?,?,?,1) ON CONFLICT(key) DO UPDATE SET "
                    "last_seen=?, times_seen=times_seen+1",
                    (key, e["ip"], e["mac"], ts, ts, ts))
        for f in findings:
            conn.execute("INSERT INTO findings (scan_id, category, title, severity,"
                         " description, evidence, advice) VALUES (?,?,?,?,?,?,?)",
                         (sid, f["category"], f["title"], f["severity"],
                          f["description"], f["evidence"], f.get("advice", "")))
        conn.commit()
        log_event("INFO", "scan",
                  f"{len(entries)} entry(ies), score {score}", sid, conn)
        for f in findings:
            if f["severity"] == "critical":
                log_event("WARN", "validation", f["title"], sid, conn)
        return sid
    finally:
        conn.close()


def run_check(do_verify: bool = False, timeout: float = 2.0,
              per_target_wait: float = 0.6, only_ips: list[str] | None = None,
              note: str = "", progress=None) -> dict:
    t0 = time.time()
    init_db()
    arp = read_arp_table()
    interfaces = interface_networks()
    gateway = default_gateway()
    entries = (arp.data or {}).get("entries", [])
    validation = validate_table(entries, interfaces, gateway) if entries else {
        "per_entry": {}, "duplicate_macs": [], "duplicate_ips": [],
        "gateway_entry": None, "gateway_shared_with": []}
    verify = None
    if do_verify and entries:
        verify = verify_entries(entries, interfaces, timeout, per_target_wait,
                                only_ips, progress)
    baseline = baseline_map()
    findings = analyse(arp, validation, verify, interfaces, gateway, baseline)
    elapsed = int((time.time() - t0) * 1000)
    sid = save_scan(arp, validation, verify, findings, interfaces, gateway, elapsed, note)
    score = risk_score(findings)
    return {"id": sid, "arp": arp, "validation": validation, "verify": verify,
            "findings": findings, "interfaces": interfaces, "gateway": gateway,
            "entries": entries, "score": score, "band": risk_band(score)[0],
            "band_colour": risk_band(score)[1], "elapsed_ms": elapsed,
            "counts": {s: sum(1 for f in findings if f["severity"] == s)
                       for s in SEVERITIES}}


# =============================================================================
# SECTION 8 - Charts (hand-drawn SVG: no CDN, no JS library, works offline)
# =============================================================================

def svg_table(entries: list[dict], validation: dict, verify_results: dict,
              gateway: dict, baseline: dict, width=940,
              title="Every entry, and what is wrong with it") -> str:
    """The signature visual: the cache drawn as the cache, with each entry's
    verdict beside it - so a clean table is visibly clean rather than an absence."""
    if not entries:
        return (f'<div class="chart-empty">{html_escape(title)}: the cache is empty</div>')
    rows = entries[:24]
    row_h, gap, pad_t = 30, 5, 30
    height = pad_t + len(rows) * (row_h + gap) + 10
    cx = [16, 150, 300, 380, 470, 700]
    parts = [f'<text x="{cx[0]}" y="18" class="hdr">IP ADDRESS</text>',
             f'<text x="{cx[1]}" y="18" class="hdr">HARDWARE ADDRESS</text>',
             f'<text x="{cx[2]}" y="18" class="hdr">IFACE</text>',
             f'<text x="{cx[3]}" y="18" class="hdr">FLAGS</text>',
             f'<text x="{cx[4]}" y="18" class="hdr">WIRE SAYS</text>',
             f'<text x="{cx[5]}" y="18" class="hdr">PROBLEMS</text>']
    for i, e in enumerate(rows):
        y = pad_t + i * (row_h + gap)
        probs = [p for p in validation.get("per_entry", {}).get(e["ip"], [])
                 if p["severity"] != "info"]
        v = verify_results.get(e["ip"]) or {}
        state = v.get("state")
        is_gw = gateway.get("ip") == e["ip"]
        if probs:
            worst = min(probs, key=lambda p: SEVERITIES.index(p["severity"]))
            colour = SEV_COLOR[worst["severity"]]
        elif state in ("conflict", "stale"):
            colour = STATE_COLOR["conflict" if state == "conflict" else "stale"]
        elif state == "valid":
            colour = STATE_COLOR["valid"]
        elif not e["complete"]:
            colour = STATE_COLOR["incomplete"]
        else:
            colour = "#31363f"
        parts.append(f'<rect x="6" y="{y}" width="{width - 12}" height="{row_h}" rx="5" '
                     f'fill="{"#1d2129" if is_gw else "#1a1e26"}" stroke="{colour}" '
                     f'stroke-width="{1.8 if is_gw else 1}"/>')
        label = e["ip"] + ("  (gateway)" if is_gw else "")
        parts.append(f'<text x="{cx[0]}" y="{y + 20}" class="cell">'
                     f'{html_escape(label)}</text>')
        parts.append(f'<text x="{cx[1]}" y="{y + 20}" class="cell">'
                     f'{html_escape(e["mac"])}</text>')
        parts.append(f'<text x="{cx[2]}" y="{y + 20}" class="cell">'
                     f'{html_escape(e["device"][:8])}</text>')
        flags = []
        if e["complete"]:
            flags.append("C")
        if e["permanent"]:
            flags.append("S")
        if e["published"]:
            flags.append("P")
        parts.append(f'<text x="{cx[3]}" y="{y + 20}" class="cell">'
                     f'{html_escape("".join(flags) or "-")}</text>')
        if state:
            wire = {"valid": "matches", "stale": "DIFFERENT", "conflict": "TWO ANSWERS",
                    "silent": "no answer"}.get(state, state)
            wcol = {"valid": "#30a46c", "stale": "#f76808", "conflict": "#e5484d"}.get(
                state, "#8b8f9b")
        else:
            wire, wcol = "not asked", "#6f7685"
        parts.append(f'<text x="{cx[4]}" y="{y + 20}" '
                     f'style="fill:{wcol};font:11.5px ui-monospace,monospace">'
                     f'{html_escape(wire)}</text>')
        summary = ", ".join(p["kind"].replace("_", " ") for p in probs[:2]) or "none"
        parts.append(f'<text x="{cx[5]}" y="{y + 20}" '
                     f'style="fill:{colour};font:11px ui-monospace,monospace">'
                     f'{html_escape(shorten(summary, 30))}</text>')
    caption = (f'{html_escape(title)} &middot; C complete, S static, P published '
               f'&middot; the gateway row is outlined')
    if len(entries) > 24:
        caption += f' &middot; showing 24 of {len(entries)}'
    return (f'<figure class="chart wide"><figcaption>{caption}</figcaption>'
            f'<svg viewBox="0 0 {width} {height}" width="100%" height="{height}" '
            f'role="img" aria-label="{html_escape(title)}">{"".join(parts)}</svg></figure>')


def svg_mac_map(validation: dict, gateway: dict, width=940,
                title="Hardware addresses holding more than one IP") -> str:
    """One node per shared hardware address, fanning out to the addresses it
    claims. A gateway sitting in one of those fans is the whole story."""
    dups = validation.get("duplicate_macs") or []
    if not dups:
        return (f'<div class="chart-empty">{html_escape(title)}: every hardware address '
                f'holds exactly one IP - nothing to draw</div>')
    dups = dups[:5]
    parts = []
    y = 20
    gw_ip = gateway.get("ip")
    for d in dups:
        ips = d["ips"][:8]
        block_h = max(40, len(ips) * 24 + 12)
        has_gw = gw_ip in ips
        colour = "#e5484d" if has_gw else "#ffb224"
        parts.append(f'<rect x="10" y="{y}" width="230" height="{block_h}" rx="7" '
                     f'fill="#1a1e26" stroke="{colour}" stroke-width="1.6"/>')
        parts.append(f'<text x="24" y="{y + 22}" class="cell">'
                     f'{html_escape(d["mac"])}</text>')
        parts.append(f'<text x="24" y="{y + 38}" class="sub">'
                     f'{html_escape(d.get("vendor") or "unknown vendor")}</text>')
        for j, ip in enumerate(ips):
            iy = y + 18 + j * 24
            is_gw = ip == gw_ip
            parts.append(f'<line x1="240" y1="{y + block_h / 2:.0f}" x2="330" y2="{iy - 5}" '
                         f'stroke="{colour}" stroke-width="1" opacity="0.5"/>')
            parts.append(f'<rect x="330" y="{iy - 18}" width="220" height="20" rx="4" '
                         f'fill="#12161d" stroke="{"#e5484d" if is_gw else "#31363f"}"/>')
            parts.append(f'<text x="340" y="{iy - 4}" class="cell">'
                         f'{html_escape(ip)}{" (GATEWAY)" if is_gw else ""}</text>')
        if has_gw:
            parts.append(f'<text x="570" y="{y + block_h / 2 + 4:.0f}" '
                         f'style="fill:#e5484d;font:700 11.5px ui-monospace,monospace">'
                         f'this address also answers for the gateway</text>')
        y += block_h + 14
    return (f'<figure class="chart wide"><figcaption>{html_escape(title)} &middot; '
            f'normal for a router doing proxy ARP &middot; red means the gateway is in the '
            f'fan</figcaption>'
            f'<svg viewBox="0 0 {width} {y + 10}" width="100%" height="{y + 10}" '
            f'role="img" aria-label="{html_escape(title)}">{"".join(parts)}</svg></figure>')


def svg_pie(items, size=180, title="Findings by severity", fmt=lambda v: f"{v:g}"):
    items = [(l, float(v), c) for (l, v, c) in items if v and v > 0]
    total = sum(v for _, v, _ in items)
    if total <= 0:
        return f'<div class="chart-empty">{html_escape(title)}: nothing to show</div>'
    cx = cy = size / 2
    r_out, r_in = size / 2 - 10, size / 2 - 42
    parts, legend, angle = [], [], -90.0
    for label, value, color in items:
        sweep = 360.0 * value / total
        if abs(sweep - 360.0) < 1e-9:
            parts.append(f'<circle cx="{cx}" cy="{cy}" r="{(r_out + r_in) / 2:.2f}" '
                         f'fill="none" stroke="{color}" stroke-width="{r_out - r_in:.2f}"/>')
        else:
            a0, a1 = math.radians(angle), math.radians(angle + sweep)
            x0, y0 = cx + r_out * math.cos(a0), cy + r_out * math.sin(a0)
            x1, y1 = cx + r_out * math.cos(a1), cy + r_out * math.sin(a1)
            x2, y2 = cx + r_in * math.cos(a1), cy + r_in * math.sin(a1)
            x3, y3 = cx + r_in * math.cos(a0), cy + r_in * math.sin(a0)
            lg = 1 if sweep > 180 else 0
            parts.append(f'<path d="M {x0:.2f} {y0:.2f} A {r_out:.2f} {r_out:.2f} 0 {lg} 1 '
                         f'{x1:.2f} {y1:.2f} L {x2:.2f} {y2:.2f} A {r_in:.2f} {r_in:.2f} 0 '
                         f'{lg} 0 {x3:.2f} {y3:.2f} Z" fill="{color}">'
                         f'<title>{html_escape(label)}: {html_escape(fmt(value))}</title>'
                         f'</path>')
        angle += sweep
        legend.append(f'<div class="lg"><i style="background:{color}"></i>'
                      f'<span>{html_escape(label)}</span><b>{html_escape(fmt(value))}</b>'
                      f'</div>')
    return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
            f'<div class="chart-row"><svg viewBox="0 0 {size} {size}" width="{size}" '
            f'height="{size}" role="img" aria-label="{html_escape(title)}">{"".join(parts)}'
            f'<text x="{cx}" y="{cy + 5}" text-anchor="middle" class="pie-n">'
            f'{html_escape(fmt(total))}</text></svg>'
            f'<div class="legend">{"".join(legend)}</div></div></figure>')


def svg_bar(items, width=430, title="", color="#5b8def", fmt=lambda v: f"{v:g}",
            colors=None):
    items = [(str(l), float(v or 0)) for l, v in items]
    if not items or all(v <= 0 for _, v in items):
        return f'<div class="chart-empty">{html_escape(title)}: nothing to show</div>'
    row_h, gap, pad_l, pad_t = 22, 7, 165, 8
    height = pad_t * 2 + len(items) * (row_h + gap)
    mx = max(v for _, v in items) or 1
    bw = width - pad_l - 62
    rows = []
    for i, (label, value) in enumerate(items):
        y = pad_t + i * (row_h + gap)
        w = max(2.0, bw * value / mx)
        c = (colors or {}).get(label, color)
        lbl = label if len(label) <= 23 else label[:22] + "\u2026"
        rows.append(
            f'<text x="{pad_l - 9}" y="{y + row_h * 0.7:.1f}" text-anchor="end" class="bl">'
            f'{html_escape(lbl)}</text>'
            f'<rect x="{pad_l}" y="{y}" width="{bw}" height="{row_h}" rx="4" class="btrack"/>'
            f'<rect x="{pad_l}" y="{y}" width="{w:.1f}" height="{row_h}" rx="4" fill="{c}">'
            f'<title>{html_escape(label)}: {html_escape(fmt(value))}</title></rect>'
            f'<text x="{pad_l + bw + 7:.1f}" y="{y + row_h * 0.7:.1f}" class="bv">'
            f'{html_escape(fmt(value))}</text>')
    return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
            f'<svg viewBox="0 0 {width} {height}" width="{width}" height="{height}" '
            f'role="img" aria-label="{html_escape(title)}">{"".join(rows)}</svg></figure>')


# =============================================================================
# SECTION 9 - Exports
# =============================================================================

def report_payload(sid=None, conn=None) -> dict:
    own = conn is None
    conn = conn or connect()
    try:
        sid = sid or latest_scan_id(conn)
        scan = scan_summary(sid, conn) if sid else None
        return {
            "tool": APP_NAME, "version": VERSION, "author": AUTHOR,
            "generated_at": now_iso(), "disclaimer": DISCLAIMER_LONG,
            "arp_has_no_authentication": NO_AUTHENTICATION,
            "a_duplicate_is_usually_not_an_attack": DUPLICATE_IS_NORMAL,
            "cache_limits": CACHE_LIMIT,
            "limitations": [
                "ARP has no authentication, so this cannot tell you which reply is "
                "legitimate - only that something disagrees.",
                "One hardware address holding several IPs is normal for a router doing "
                "proxy ARP, a firewall, or a virtualisation host.",
                "It sees only this machine's cache and this machine's segment - ARP does "
                "not cross a router.",
                "The cache holds only what this machine has recently talked to, so an "
                "absent device is not necessarily absent from the network.",
                "Silence during verification means the device did not answer - not that "
                "the cached entry is wrong, and not that it is right.",
                "Verification confirms an entry at one moment only; an ARP cache can be "
                "overwritten at any time by anything on the segment.",
                "Read-only: no ARP entry is ever added, deleted or altered.",
            ],
            "scan": scan,
            "observations": [dict(r) for r in q(
                "SELECT * FROM observations WHERE scan_id=? ORDER BY ip", (sid,), conn)]
            if sid else [],
            "findings": [dict(r) for r in q(
                "SELECT category,title,severity,description,evidence,advice FROM findings "
                "WHERE scan_id=? ORDER BY CASE severity WHEN 'critical' THEN 0 "
                "WHEN 'high' THEN 1 WHEN 'medium' THEN 2 WHEN 'low' THEN 3 ELSE 4 END, id",
                (sid,), conn)] if sid else [],
            "pairs": [dict(r) for r in q("SELECT * FROM pairs ORDER BY ip", (), conn)],
            "history": [dict(r) for r in q(
                "SELECT id, ts, score, band, entries FROM scans ORDER BY id DESC LIMIT 40",
                (), conn)][::-1],
        }
    finally:
        if own:
            conn.close()


def export_json(sid=None) -> str:
    return json.dumps(report_payload(sid), indent=2, default=str)


def export_csv(sid=None) -> str:
    conn = connect()
    try:
        sid = sid or latest_scan_id(conn)
        scan = scan_summary(sid, conn)
        buf = io.StringIO()
        w = csv.writer(buf, lineterminator="\n")
        w.writerow([f"# {APP_NAME} v{VERSION} by {AUTHOR}"])
        w.writerow([f"# scan={sid} generated={now_iso()}"])
        w.writerow([f"# {DISCLAIMER_SHORT}"])
        w.writerow(["# ARP has no authentication - this cannot tell you which reply is "
                    "legitimate, only that something disagrees."])
        if not scan:
            return buf.getvalue()
        w.writerow([])
        w.writerow(["## Check"])
        w.writerow(["hostname", "entries", "complete", "incomplete", "static",
                    "duplicate_macs", "duplicate_ips", "conflicts", "stale",
                    "gateway_ip", "gateway_mac", "score", "band", "verified"])
        w.writerow([scan["hostname"], scan["entries"], scan["complete"],
                    scan["incomplete"], scan["static"], scan["duplicate_macs"],
                    scan["duplicate_ips"], scan["conflicts"], scan["stale"],
                    scan["gateway_ip"], scan["gateway_mac"], scan["score"],
                    scan["band"], scan["verified"]])
        w.writerow([])
        w.writerow(["## Entries"])
        w.writerow(["ip", "mac", "device", "complete", "permanent", "published",
                    "vendor", "problems", "verify_state", "reply_macs"])
        for r in q("SELECT * FROM observations WHERE scan_id=? ORDER BY ip", (sid,), conn):
            w.writerow([r["ip"], r["mac"], r["device"], r["complete"], r["permanent"],
                        r["published"], r["vendor"], r["problems"], r["verify_state"],
                        r["reply_macs"]])
        w.writerow([])
        w.writerow(["## Findings"])
        w.writerow(["severity", "category", "title", "description", "advice"])
        for r in q("SELECT * FROM findings WHERE scan_id=? ORDER BY id", (sid,), conn):
            w.writerow([r["severity"], r["category"], r["title"], r["description"],
                        r["advice"]])
        return buf.getvalue()
    finally:
        conn.close()


def export_html(sid=None) -> str:
    conn = connect()
    try:
        p = report_payload(sid, conn)
        scan, esc = p["scan"], html_escape
        if not scan:
            return "<!doctype html><html><body><h1>No checks recorded</h1></body></html>"
        counts = {s: scan[s] or 0 for s in SEVERITIES}
        payload = scan.get("payload") or {}
        entries = payload.get("entries") or []
        validation = {**(payload.get("validation") or {}),
                      "per_entry": payload.get("per_entry") or {}}
        table = svg_table(entries, validation, payload.get("verify") or {},
                          payload.get("gateway") or {}, {})
        macmap = svg_mac_map(validation, payload.get("gateway") or {})
        pie = svg_pie([(s, counts[s], SEV_COLOR[s]) for s in SEVERITIES])
        kinds: dict[str, int] = {}
        for probs in (payload.get("per_entry") or {}).values():
            for pr in probs:
                if pr["severity"] != "info":
                    kinds[pr["kind"].replace("_", " ")] = \
                        kinds.get(pr["kind"].replace("_", " "), 0) + 1
        bar = (svg_bar(sorted(kinds.items(), key=lambda x: -x[1])[:8],
                       title="Problems by kind", color="#f76808") if kinds else "")
        frows = "".join(
            f'<tr><td><span class="pill" style="background:{SEV_COLOR[f["severity"]]}">'
            f'{esc(f["severity"].upper())}</span></td>'
            f'<td><b>{esc(f["title"])}</b>'
            f'<div class="desc">{esc(f["description"])}</div>'
            + (f'<pre>{esc(f["evidence"])}</pre>' if f["evidence"] else "")
            + (f'<div class="means"><b>What to make of it:</b> {esc(f["advice"])}</div>'
               if f["advice"] else "") + "</td></tr>" for f in p["findings"])
        limits = "".join(f"<li>{esc(x)}</li>" for x in p["limitations"])
        return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{APP_SHORT} - {esc(scan['hostname'] or '')}</title><style>
 body{{font:14px/1.55 ui-sans-serif,system-ui,'Segoe UI',Roboto,sans-serif;margin:0;
      background:#0f1115;color:#e6e8ee}}
 .wrap{{max-width:1100px;margin:0 auto;padding:28px 20px 60px}}
 h1{{font-size:22px;margin:0 0 4px}} .meta{{color:#8b8f9b;font-size:12.5px}}
 h2{{font-size:12px;text-transform:uppercase;letter-spacing:.15em;color:#8b8f9b;
     margin:30px 0 12px;border-bottom:1px solid #262a33;padding-bottom:8px}}
 .grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:10px;margin:18px 0}}
 .card{{background:#171a21;border:1px solid #262a33;border-radius:10px;padding:12px 14px}}
 .card .n{{font-size:21px;font-weight:700;font-family:ui-monospace,monospace}}
 .card .l{{font-size:10.5px;text-transform:uppercase;letter-spacing:.11em;color:#8b8f9b}}
 table{{width:100%;border-collapse:collapse;background:#171a21;border:1px solid #262a33;
        border-radius:10px;overflow:hidden;font-size:12.7px}}
 th{{text-align:left;font-size:10.5px;letter-spacing:.11em;text-transform:uppercase;
     color:#8b8f9b;padding:9px 11px;border-bottom:1px solid #262a33;background:#1c2029}}
 td{{padding:8px 11px;border-bottom:1px solid #1e222a;vertical-align:top}}
 .mono{{font-family:ui-monospace,Menlo,monospace;font-size:11.5px;word-break:break-word}}
 .pill{{color:#0f1115;font-weight:700;font-size:10px;padding:2px 8px;border-radius:20px}}
 .desc{{color:#b6bac4;margin-top:4px;max-width:84ch}}
 .means{{margin-top:6px;color:#8fd3b0;font-size:12.4px;max-width:84ch}}
 pre{{background:#0f1115;border:1px solid #262a33;border-radius:6px;padding:9px;
      font-family:ui-monospace,monospace;font-size:11.5px;margin:6px 0 0;overflow:auto;
      white-space:pre-wrap;color:#b6bac4;max-height:300px}}
 .warn{{background:#231a12;border:1px solid #5a3b1c;color:#ffcf9e;padding:12px 14px;
        border-radius:10px;font-size:12.5px;margin:14px 0;white-space:pre-wrap}}
 .note{{background:#12202a;border:1px solid #1c4a5e;color:#a8d8e8;padding:11px 14px;
        border-radius:10px;font-size:12.5px;margin:14px 0}}
 .note ul{{margin:6px 0 0 18px;padding:0}} .note li{{margin:3px 0}}
 .danger{{background:#2a1216;border:1px solid #6b2229;color:#ffc9cd;padding:12px 14px;
        border-radius:10px;font-size:12.8px;margin:14px 0;font-weight:600}}
 .charts{{display:flex;gap:18px;flex-wrap:wrap;align-items:flex-start;margin-bottom:14px}}
 .chart{{margin:0;background:#171a21;border:1px solid #262a33;border-radius:10px;
   padding:14px 16px}}
 .chart.wide{{width:100%}}
 .chart figcaption{{font-size:10.5px;letter-spacing:.12em;text-transform:uppercase;
   color:#8b8f9b;margin-bottom:10px;font-family:ui-monospace,monospace}}
 .chart-row{{display:flex;gap:16px;align-items:center;flex-wrap:wrap}}
 .chart-empty{{background:#171a21;border:1px dashed #31363f;border-radius:10px;padding:18px;
   color:#8b8f9b;font-size:12.5px}}
 .legend{{display:flex;flex-direction:column;gap:6px;min-width:130px}}
 .lg{{display:flex;align-items:center;gap:7px;font-size:12.5px}}
 .lg i{{width:11px;height:11px;border-radius:3px}} .lg span{{flex:1}}
 text.bl{{fill:#8b8f9b;font:10.5px ui-monospace,monospace}}
 text.bv{{fill:#e6e8ee;font:11px ui-monospace,monospace}}
 text.hdr{{fill:#6f7685;font:9.5px ui-monospace,monospace;letter-spacing:.12em}}
 text.cell{{fill:#e6e8ee;font:11.5px ui-monospace,monospace}}
 text.sub{{fill:#6f7685;font:10px ui-monospace,monospace}}
 text.pie-n{{fill:#e6e8ee;font:700 16px ui-monospace,monospace}}
 rect.btrack{{fill:#1e222a}}
 footer{{margin-top:36px;color:#6f7685;font-size:12px;border-top:1px solid #262a33;
   padding-top:14px}}
</style></head><body><div class="wrap">
<h1>ARP cache validation</h1>
<div class="meta">{esc(scan['hostname'])} &middot; {ts_pretty(scan['ts'])} &middot;
 {scan['elapsed_ms']} ms &middot; from {esc(scan['source'] or '?')}
 {'&middot; entries were re-asked' if scan['verified'] else '&middot; not verified against the network'}
 <br>gateway {esc(scan['gateway_ip'] or '?')} at {esc(scan['gateway_mac'] or '?')}</div>
{f'<div class="danger">{scan["conflicts"]} address(es) were claimed by more than one machine.</div>'
 if scan['conflicts'] else ''}
<div class="note"><b>ARP has no authentication.</b>
 {esc(p['arp_has_no_authentication'])}<ul>{limits}</ul></div>
<div class="warn">{esc(DISCLAIMER_LONG)}</div>
<div class="grid">
 <div class="card"><div class="l">Entries</div><div class="n">{scan['entries']}</div>
  <div class="l">{scan['complete']} complete</div></div>
 <div class="card"><div class="l">Shared MACs</div>
  <div class="n" style="color:{'#ffb224' if scan['duplicate_macs'] else '#30a46c'}">
   {scan['duplicate_macs']}</div></div>
 <div class="card"><div class="l">Conflicts</div>
  <div class="n" style="color:{'#e5484d' if scan['conflicts'] else '#30a46c'}">
   {scan['conflicts']}</div></div>
 <div class="card"><div class="l">Stale</div>
  <div class="n" style="color:{'#f76808' if scan['stale'] else '#30a46c'}">
   {scan['stale']}</div></div>
 <div class="card"><div class="l">Verdict</div>
  <div class="n" style="font-size:14px;color:{scan['band_colour']}">
   {esc(scan['band'] or '')}</div><div class="l">score {scan['score']}</div></div>
</div>
<h2>The cache</h2><div class="charts">{table}</div>
<h2>Shared hardware addresses</h2><div class="charts">{macmap}</div>
<h2>Analytics</h2><div class="charts">{pie}{bar}</div>
<h2>Findings ({len(p['findings'])})</h2>
{'<table><tr><th>Severity</th><th>Detail</th></tr>' + frows + '</table>'
 if frows else '<div class="chart-empty">No findings.</div>'}
<footer>Generated by {APP_NAME} v{VERSION} &middot; {AUTHOR} &middot; {GITHUB}<br>
 No ARP entry was added, deleted or altered. Only this machine's cache and this machine's
 segment were examined.</footer>
</div></body></html>"""
    finally:
        conn.close()


# =============================================================================
# SECTION 10 - Web application (no CDN, no JS libraries)
# =============================================================================

CSS = """
:root{--bg:#0f1115;--panel:#171a21;--panel-2:#1c2029;--line:#262a33;--line-2:#31363f;
 --tx:#e6e8ee;--tx-dim:#8b8f9b;--tx-mid:#b6bac4;--accent:#22b8cf;--ok:#30a46c;
 --warn:#ffb224;--crit:#e5484d;--good:#8fd3b0;
 --mono:ui-monospace,SFMono-Regular,'JetBrains Mono',Menlo,Consolas,'Courier New',monospace;}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);
 font:14px/1.55 ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,Helvetica,Arial,sans-serif}
a{color:var(--accent);text-decoration:none} a:hover{text-decoration:underline}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:4px}
header.top{border-bottom:1px solid var(--line);background:var(--panel);position:sticky;top:0;z-index:9}
.hd{max-width:1200px;margin:0 auto;padding:11px 20px;display:flex;align-items:center;gap:14px;
 flex-wrap:wrap}
.brand{font-family:var(--mono);font-weight:700;letter-spacing:-.4px;font-size:15px}
.brand b{color:var(--accent)}
.brand small{display:block;font-weight:400;font-size:10px;letter-spacing:.14em;
 text-transform:uppercase;color:var(--tx-dim)}
nav{display:flex;gap:2px;margin-left:auto;flex-wrap:wrap}
nav a{font-family:var(--mono);font-size:11.5px;letter-spacing:.05em;text-transform:uppercase;
 padding:6px 10px;border-radius:6px;color:var(--tx-dim)}
nav a:hover{background:var(--panel-2);color:var(--tx);text-decoration:none}
nav a.on{background:var(--accent);color:#0b0d10;font-weight:600}
.wrap{max-width:1200px;margin:0 auto;padding:20px 20px 70px}
.banner{background:#12202a;border:1px solid #1c4a5e;color:#a8d8e8;padding:10px 14px;
 border-radius:9px;font-size:12.3px;margin-bottom:12px;line-height:1.5}
.banner.warn{background:#231a12;border-color:#5a3b1c;color:#ffcf9e}
.banner.bad{background:#2a1216;border-color:#6b2229;color:#ffc9cd}
.banner b{color:#fff} .banner ul{margin:6px 0 0 18px;padding:0} .banner li{margin:3px 0}
h1{font-size:19px;margin:0 0 3px;letter-spacing:-.3px}
h2{font-family:var(--mono);font-size:11.5px;letter-spacing:.16em;text-transform:uppercase;
 color:var(--tx-dim);margin:24px 0 12px;padding-bottom:8px;border-bottom:1px solid var(--line)}
.sub{color:var(--tx-dim);font-size:12.5px;margin-bottom:14px}
.sub2{color:var(--tx-dim);font-size:11px;font-family:var(--mono)}
.bar{display:flex;gap:9px;align-items:center;flex-wrap:wrap;margin:0 0 16px}
.btn{font-family:var(--mono);font-size:12px;padding:8px 13px;border-radius:7px;cursor:pointer;
 border:1px solid var(--line-2);background:var(--panel-2);color:var(--tx);display:inline-block}
.btn:hover{border-color:var(--accent);text-decoration:none}
.btn.primary{background:var(--accent);border-color:var(--accent);color:#0b0d10;font-weight:700}
.btn.danger{border-color:#6b2229;color:#ffc9cd}
.btn.tiny{padding:3px 8px;font-size:10.5px}
input[type=text],select{font-family:var(--mono);font-size:12px;padding:7px 9px;
 background:var(--panel-2);color:var(--tx);border:1px solid var(--line-2);border-radius:7px}
.grid{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(132px,1fr));margin:14px 0}
.card{background:var(--panel);border:1px solid var(--line);border-radius:11px;padding:13px 15px}
.card .l{font-family:var(--mono);font-size:10.5px;letter-spacing:.13em;text-transform:uppercase;
 color:var(--tx-dim)}
.card .n{font-size:21px;font-weight:700;line-height:1.3;font-family:var(--mono)}
table{width:100%;border-collapse:collapse;background:var(--panel);border:1px solid var(--line);
 border-radius:11px;overflow:hidden;font-size:12.7px}
th{text-align:left;font-family:var(--mono);font-size:10.5px;letter-spacing:.11em;
 text-transform:uppercase;color:var(--tx-dim);padding:9px 11px;border-bottom:1px solid var(--line);
 background:var(--panel-2);white-space:nowrap}
td{padding:8px 11px;border-bottom:1px solid #1e222a;vertical-align:top}
tr:last-child td{border-bottom:none} tr:hover td{background:#1b1f27}
.mono{font-family:var(--mono);font-size:11.8px;word-break:break-word}
.num{font-family:var(--mono);font-size:11.8px;text-align:right}
.pill{display:inline-block;color:#0b0d10;font-weight:700;font-size:10px;padding:2px 8px;
 border-radius:20px;letter-spacing:.06em;font-family:var(--mono);white-space:nowrap}
.tag{display:inline-block;font-family:var(--mono);font-size:10px;padding:1px 6px;border-radius:5px;
 border:1px solid var(--line-2);color:var(--tx-dim);white-space:nowrap;margin-left:4px}
.tag.good{border-color:#1e5138;color:#7fd9ab} .tag.bad{border-color:#5a2326;color:#ff9b9e}
.desc{color:var(--tx-mid);margin-top:4px;max-width:84ch}
.means{margin-top:6px;color:var(--good);font-size:12.4px;max-width:84ch}
pre{background:var(--bg);border:1px solid var(--line);border-radius:6px;padding:9px 11px;
 font-family:var(--mono);font-size:11.5px;margin:6px 0 0;max-height:300px;overflow:auto;
 white-space:pre-wrap;color:var(--tx-mid)}
.charts{display:flex;gap:18px;flex-wrap:wrap;align-items:flex-start;margin-bottom:14px}
.chart{margin:0;background:var(--panel);border:1px solid var(--line);border-radius:11px;
 padding:14px 16px}
.chart.wide{width:100%}
.chart figcaption{font-family:var(--mono);font-size:10.5px;letter-spacing:.13em;
 text-transform:uppercase;color:var(--tx-dim);margin-bottom:10px}
.chart-row{display:flex;gap:16px;align-items:center;flex-wrap:wrap}
.chart-empty{background:var(--panel);border:1px dashed var(--line-2);border-radius:11px;
 padding:20px;color:var(--tx-dim);font-size:12.5px;flex:1;min-width:240px}
.legend{display:flex;flex-direction:column;gap:6px;min-width:130px}
.lg{display:flex;align-items:center;gap:7px;font-size:12.5px}
.lg i{width:11px;height:11px;border-radius:3px;flex:none} .lg span{flex:1}
.lg b{font-family:var(--mono)}
text.bl{fill:#8b8f9b;font:10.5px var(--mono)} text.bv{fill:#e6e8ee;font:11px var(--mono)}
text.hdr{fill:#6f7685;font:9.5px var(--mono);letter-spacing:.12em}
text.cell{fill:#e6e8ee;font:11.5px var(--mono)}
text.sub{fill:#6f7685;font:10px var(--mono)}
text.pie-n{fill:#e6e8ee;font:700 16px var(--mono)}
rect.btrack{fill:#1e222a}
.empty{background:var(--panel);border:1px dashed var(--line-2);border-radius:11px;padding:28px;
 text-align:center;color:var(--tx-dim)}
.empty b{display:block;color:var(--tx);margin-bottom:6px;font-size:15px}
footer{max-width:1200px;margin:0 auto;padding:16px 20px 40px;color:#6f7685;font-size:11.5px;
 border-top:1px solid var(--line);line-height:1.7}
.lvl-ERROR{color:var(--crit)} .lvl-WARN{color:var(--warn)} .lvl-INFO{color:var(--tx-dim)}
@media (max-width:640px){.hd{padding:10px 14px} .wrap{padding:14px 14px 50px}
 nav{margin-left:0;width:100%} .card .n{font-size:18px} table{font-size:12px}
 th,td{padding:7px 8px}}
"""

BASE_TPL = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{{ page }} - """ + APP_SHORT + """</title><style>""" + CSS + """</style></head><body>
<header class="top"><div class="hd">
 <div class="brand"><b>ARPCHECK</b> <small>entry validator</small></div>
 <nav>
  <a href="{{ url_for('page_overview') }}" class="{{ 'on' if nav=='overview' }}">Overview</a>
  <a href="{{ url_for('page_pairs') }}" class="{{ 'on' if nav=='pairs' }}">Pairs</a>
  <a href="{{ url_for('page_scans') }}" class="{{ 'on' if nav=='scans' }}">Checks</a>
  <a href="{{ url_for('page_learn') }}" class="{{ 'on' if nav=='learn' }}">Learn</a>
  <a href="{{ url_for('page_logs') }}" class="{{ 'on' if nav=='logs' }}">Logs</a>
 </nav></div></header>
<div class="wrap">
 <div class="banner"><b>ARP has no authentication.</b> """ + NO_AUTHENTICATION + """</div>
 {% if error %}<div class="banner bad"><b>That failed:</b> {{ error }}</div>{% endif %}
 {% if flash %}<div class="banner">{{ flash }}</div>{% endif %}
 {% block body %}{% endblock %}
</div>
<footer>""" + APP_NAME + """ v""" + VERSION + """ &middot; built by """ + AUTHOR + """ &middot;
 <a href=\"""" + GITHUB + """\" rel="noopener">GitHub</a> &middot;
 <a href=\"""" + LINKEDIN + """\" rel="noopener">LinkedIn</a><br>
 The consistency checks read the cache and transmit nothing. Verification broadcasts ARP
 requests - it is never run without asking. No ARP entry is ever added, deleted or altered.
</footer></body></html>"""

RUNBAR_TPL = """
<div class="bar">
 <form method="post" action="{{ url_for('do_check') }}">
  <button class="btn primary" type="submit">Validate the cache</button></form>
 <form method="post" action="{{ url_for('do_verify') }}"
  onsubmit="return confirm('This BROADCASTS an ARP request for every cached address. That is ordinary traffic, but it puts this machine in front of everything on the segment and will populate other machines\\' caches. Continue?')">
  <button class="btn danger" type="submit">Validate and re-ask the network</button></form>
 {% if scan %}
 <a class="btn" href="{{ url_for('export', fmt='html') }}?scan={{ scan.id }}">Export HTML</a>
 <a class="btn" href="{{ url_for('export', fmt='json') }}?scan={{ scan.id }}">JSON</a>
 <a class="btn" href="{{ url_for('export', fmt='csv') }}?scan={{ scan.id }}">CSV</a>
 {% endif %}
</div>"""

EMPTY_TPL = """{% extends 'base.html' %}{% block body %}
<h1>Overview</h1>
""" + RUNBAR_TPL + """
<div class="empty"><b>Nothing checked yet</b>
 The consistency checks ask whether each entry makes sense on its own - the right subnet, a
 usable hardware address, one machine per address. They need no privileges and transmit
 nothing. Verification then re-asks the network whether each entry is still true.
 <div class="mono" style="margin-top:12px;color:var(--tx-dim)">
  from the terminal: python3 arpcheck.py check</div>
</div>{% endblock %}"""

OVERVIEW_TPL = """{% extends 'base.html' %}{% block body %}
<h1>Overview</h1>
<div class="sub">Check #{{ scan.id }} &middot; {{ ts_pretty(scan.ts) }} &middot;
 {{ scan.elapsed_ms }} ms &middot; from {{ scan.source }} &middot;
 {{ 'entries were re-asked' if scan.verified else 'not verified against the network' }}</div>
""" + RUNBAR_TPL + """
{% if scan.detail %}<div class="banner warn"><b>Partial:</b> {{ scan.detail }}</div>{% endif %}
{% if scan.conflicts %}
<div class="banner bad"><b>{{ scan.conflicts }} address(es) were claimed by more than one
 machine.</b> ARP cannot tell you which is real - but on a healthy network only one should
 answer.</div>
{% endif %}
<div class="grid">
 <div class="card"><div class="l">Entries</div><div class="n">{{ scan.entries }}</div>
  <div class="l">{{ scan.complete }} complete</div></div>
 <div class="card"><div class="l">Shared MACs</div>
  <div class="n" style="color:{{ '#ffb224' if scan.duplicate_macs else '#30a46c' }}">
   {{ scan.duplicate_macs }}</div></div>
 <div class="card"><div class="l">Conflicts</div>
  <div class="n" style="color:{{ '#e5484d' if scan.conflicts else '#30a46c' }}">
   {{ scan.conflicts }}</div></div>
 <div class="card"><div class="l">Stale</div>
  <div class="n" style="color:{{ '#f76808' if scan.stale else '#30a46c' }}">
   {{ scan.stale }}</div></div>
 <div class="card"><div class="l">Verdict</div>
  <div class="n" style="font-size:14px;color:{{ scan.band_colour }}">{{ scan.band }}</div>
  <div class="l">score {{ scan.score }}</div></div>
</div>
<div class="banner"><b>Gateway:</b> {{ scan.gateway_ip or 'none' }} at
 {{ scan.gateway_mac or 'not cached' }}. Everything leaving this subnet goes to that
 hardware address, which makes it the entry worth getting right.</div>
<h2>The cache</h2><div class="charts">{{ table|safe }}</div>
<h2>Shared hardware addresses</h2><div class="charts">{{ macmap|safe }}</div>
<h2>Analytics</h2><div class="charts">{{ pie|safe }}</div>
<h2>Findings ({{ findings|length }})</h2>
{% if findings %}
<table><tr><th>Severity</th><th>Detail</th></tr>
{% for f in findings %}
<tr><td><span class="pill" style="background:{{ sev[f.severity] }}">
 {{ f.severity|upper }}</span></td>
 <td><b>{{ f.title }}</b><div class="desc">{{ f.description }}</div>
  {% if f.evidence %}<pre>{{ f.evidence }}</pre>{% endif %}
  {% if f.advice %}<div class="means"><b>What to make of it:</b> {{ f.advice }}</div>
  {% endif %}</td></tr>
{% endfor %}</table>
{% else %}<div class="empty">No findings.</div>{% endif %}
{% endblock %}"""

PAIRS_TPL = """{% extends 'base.html' %}{% block body %}
<h1>Address pairs</h1>
<div class="sub">{{ rows|length }} IP and hardware address pairing(s) seen. Approving one
 stops it being reported - useful for a router that legitimately answers for several
 addresses.</div>
<div class="bar"><form method="get" style="display:flex;gap:8px;flex-wrap:wrap">
 <input type="text" name="qq" value="{{ f_q }}" placeholder="filter by address">
 <button class="btn" type="submit">Filter</button>
 <a class="btn" href="{{ url_for('page_pairs') }}">Reset</a>
</form></div>
{% if rows %}
<table><tr><th>IP</th><th>Hardware address</th><th>Seen</th><th>First</th><th>Last</th>
 <th></th></tr>
{% for r in rows %}<tr>
 <td class="mono">{{ r.ip }}</td>
 <td class="mono">{{ r.mac }}{% if r.approved %}<span class="tag good">approved</span>
  {% endif %}{% if r.label %}<div class="sub2">{{ r.label }}</div>{% endif %}</td>
 <td class="num">{{ r.times_seen }}</td>
 <td class="mono">{{ (r.first_seen or '')[:16].replace('T',' ') }}</td>
 <td class="mono">{{ ago(r.last_seen) }}</td>
 <td>{% if r.approved %}
   <form method="post" action="{{ url_for('do_revoke') }}" style="display:inline">
    <input type="hidden" name="key" value="{{ r.key }}">
    <button class="btn tiny" type="submit">revoke</button></form>
  {% else %}
   <form method="post" action="{{ url_for('do_approve') }}" style="display:inline">
    <input type="hidden" name="key" value="{{ r.key }}">
    <button class="btn tiny" type="submit">approve</button></form>
  {% endif %}</td></tr>
{% endfor %}</table>
{% else %}<div class="empty"><b>No pairs recorded</b> Run a check first.</div>{% endif %}
{% endblock %}"""

SCANS_TPL = """{% extends 'base.html' %}{% block body %}
<h1>Checks</h1><div class="sub">{{ rows|length }} check(s) stored locally.</div>
{% if rows %}
<table><tr><th>#</th><th>When</th><th>Entries</th><th>Shared</th><th>Conflicts</th>
 <th>Stale</th><th>Score</th><th>Verified</th><th></th></tr>
{% for r in rows %}<tr>
 <td class="mono">#{{ r.id }}</td>
 <td class="mono">{{ r.ts[:19].replace('T',' ') }}</td>
 <td class="num">{{ r.entries }}</td>
 <td class="num">{{ r.duplicate_macs }}</td>
 <td class="num" style="color:{{ '#e5484d' if r.conflicts else '#8b8f9b' }}">
  {{ r.conflicts }}</td>
 <td class="num">{{ r.stale }}</td>
 <td class="num" style="color:{{ bandcol(r.score) }}">{{ r.score }}</td>
 <td class="sub2">{{ 'yes' if r.verified else 'no' }}</td>
 <td><a class="btn" href="{{ url_for('page_overview') }}?scan={{ r.id }}">view</a></td>
</tr>{% endfor %}</table>
{% else %}<div class="empty"><b>Nothing checked yet</b></div>{% endif %}
{% endblock %}"""

LEARN_TPL = """{% extends 'base.html' %}{% block body %}
<h1>What an ARP entry is, and what can be wrong with it</h1>
<div class="banner bad"><b>ARP has no authentication.</b> A machine broadcasts "who has this
 address" and believes whichever answer arrives - there is no signature, no challenge, and
 nothing to check the reply against. The last answer wins. That is not a bug in any
 implementation; it is how the protocol was designed in 1982, and everything below follows
 from it.</div>
<h2>Two different questions</h2>
<div class="desc"><b>Is the entry internally consistent?</b> An address outside the
 interface's own subnet cannot be reached by ARP at all. A broadcast or multicast hardware
 address in a unicast entry is meaningless. One hardware address claiming several IP
 addresses is either proxy ARP or somebody answering for addresses that are not theirs. None
 of this touches the network - it is arithmetic on the cache, the interface addresses and the
 routing table, so it needs no privileges and nothing on the wire can fool it.<br><br>
 <b>Is the entry still true?</b> A cached entry is a claim that nothing revalidates until it
 ages out. Verification re-asks and compares. One different answer means the cache is stale;
 <b>two answers to one question</b> means two machines claim one address.</div>
<h2>The gateway is the entry worth stealing</h2>
<div class="desc">Everything leaving the subnet is sent to the gateway's hardware address. An
 attacker who answers for the gateway sees all of it, and needs to convince only one machine.
 That is why a hardware address covering both the gateway and other hosts is reported at the
 highest severity here - and also why <b>a static entry for the gateway</b> is a cheap and
 genuinely effective defence.</div>
<h2>A duplicate is usually not an attack</h2>
<div class="banner warn">One hardware address holding several IP addresses is completely
 normal for a router doing proxy ARP, a firewall with secondary addresses, or a
 virtualisation host. What makes it interesting is where it appears, and most of all whether
 it covers the gateway. Approve the ones you recognise and later checks stay quiet about
 them.</div>
<h2>Flags worth understanding</h2>
<div class="desc"><b>Complete</b> means a reply was received. An <b>incomplete</b> entry means
 the request went out and nothing answered - ordinary for an address not in use, though a
 large number at once is the trace a subnet sweep leaves in the cache of the machine doing
 the sweeping.<br><br>
 <b>Static</b> entries were configured by hand and never age out: a good defence, and also a
 wrong entry that stays wrong until somebody removes it. <b>Published</b> means this machine
 answers ARP for an address that is not its own, which is deliberate on a router and worth
 confirming anywhere else.</div>
<h2>What this cannot see</h2>
<div class="desc">Only this machine's cache and this machine's segment. <b>ARP does not cross
 a router</b>, so nothing beyond the gateway appears here at all. The cache holds only what
 this machine has recently talked to, so a device that is absent from it is not necessarily
 absent from the network.<br><br>
 During verification, silence means the device did not answer - it may be off, asleep or
 filtering. That does not mean the cached entry is wrong, and it does not mean it is right.
 And a confirmation is a confirmation at one moment: an ARP cache can be overwritten at any
 time by anything on the segment.</div>
{% endblock %}"""

LOGS_TPL = """{% extends 'base.html' %}{% block body %}
<h1>Logs</h1><div class="sub">Stored locally in {{ dbfile }}.</div>
<div class="bar"><form method="get" style="display:flex;gap:8px;flex-wrap:wrap">
 <select name="level"><option value="">All levels</option>
  {% for l in ['INFO','WARN','ERROR'] %}<option value="{{ l }}" {{ 'selected' if l==f_level }}>
   {{ l }}</option>{% endfor %}</select>
 <input type="text" name="qq" value="{{ f_q }}" placeholder="search">
 <button class="btn" type="submit">Filter</button>
 <a class="btn" href="{{ url_for('page_logs') }}">Reset</a>
</form></div>
{% if rows %}
<table><tr><th>Time (UTC)</th><th>Level</th><th>Source</th><th>Message</th><th>Check</th></tr>
{% for e in rows %}<tr><td class="mono">{{ e.ts[:19].replace('T',' ') }}</td>
 <td class="mono lvl-{{ e.level }}"><b>{{ e.level }}</b></td>
 <td class="mono">{{ e.source }}</td><td>{{ e.message }}</td>
 <td class="mono">{{ ('#' ~ e.scan_id) if e.scan_id else '-' }}</td></tr>{% endfor %}</table>
{% else %}<div class="empty"><b>No log entries match</b></div>{% endif %}
{% endblock %}"""

TEMPLATES = {"base.html": BASE_TPL, "empty.html": EMPTY_TPL, "overview.html": OVERVIEW_TPL,
             "pairs.html": PAIRS_TPL, "scans.html": SCANS_TPL, "learn.html": LEARN_TPL,
             "logs.html": LOGS_TPL}

try:
    from flask import (Flask, Response, jsonify, redirect, render_template, request, url_for)
    from jinja2 import ChoiceLoader, DictLoader
    HAVE_FLASK = True
except Exception:  # pragma: no cover
    HAVE_FLASK = False


def build_app():
    if not HAVE_FLASK:
        raise SystemExit("Flask is not installed. Install it with:  pip install flask\n"
                         "(The CLI works without Flask; only the web app needs it.)")
    app = Flask(__name__)
    app.jinja_loader = ChoiceLoader([DictLoader(TEMPLATES), app.jinja_loader])

    def bandcol(score):
        return risk_band(score or 0)[1]

    def ctx(nav, **kw):
        base = {"nav": nav, "page": nav.capitalize(), "sev": SEV_COLOR,
                "severities": SEVERITIES, "ts_pretty": ts_pretty, "ago": ago,
                "bandcol": bandcol, "scan": None,
                "error": request.args.get("error"),
                "flash": request.args.get("flash")}
        base.update(kw)
        return base

    @app.route("/")
    def page_overview():
        conn = connect()
        try:
            init_db(conn)
            try:
                sid = int(request.args.get("scan", "") or 0)
            except ValueError:
                sid = 0
            scan = scan_summary(sid, conn) if sid else None
            if not scan:
                sid = latest_scan_id(conn)
                scan = scan_summary(sid, conn) if sid else None
            if not scan:
                return render_template("empty.html", **ctx("overview"))
            p = report_payload(scan["id"], conn)
            payload = scan.get("payload") or {}
            validation = {**(payload.get("validation") or {}),
                          "per_entry": payload.get("per_entry") or {}}
            counts = {s: scan[s] or 0 for s in SEVERITIES}
            return render_template("overview.html", **ctx(
                "overview", scan=scan, findings=p["findings"],
                table=svg_table(payload.get("entries") or [], validation,
                                payload.get("verify") or {},
                                payload.get("gateway") or {}, baseline_map(conn)),
                macmap=svg_mac_map(validation, payload.get("gateway") or {}),
                pie=svg_pie([(s, counts[s], SEV_COLOR[s]) for s in SEVERITIES])))
        finally:
            conn.close()

    @app.post("/check")
    def do_check():
        import urllib.parse as up
        try:
            res = run_check(do_verify=False, note="from the web UI")
        except Exception as e:
            log_event("ERROR", "scan", str(e))
            return redirect(url_for("page_overview") + "?error=" + up.quote(str(e)))
        return redirect(url_for("page_overview") + f"?scan={res['id']}")

    @app.post("/verify")
    def do_verify():
        import urllib.parse as up
        try:
            res = run_check(do_verify=True, note="from the web UI (verified)")
        except Exception as e:
            log_event("ERROR", "scan", str(e))
            return redirect(url_for("page_overview") + "?error=" + up.quote(str(e)))
        return redirect(url_for("page_overview") + f"?scan={res['id']}&flash="
                        + up.quote("ARP requests were broadcast. Every machine on the "
                                   "segment has now seen this machine's address."))

    @app.route("/pairs")
    def page_pairs():
        conn = connect()
        try:
            init_db(conn)
            term = request.args.get("qq", "").strip()
            sql, args = "SELECT * FROM pairs WHERE 1=1", []
            if term:
                sql += " AND (ip LIKE ? OR mac LIKE ?)"
                args += [f"%{term}%"] * 2
            sql += " ORDER BY approved DESC, ip LIMIT 500"
            rows = [dict(r) for r in q(sql, tuple(args), conn)]
            for r in rows:
                r["approved"] = bool(r["approved"])
            return render_template("pairs.html", **ctx("pairs", rows=rows, f_q=term))
        finally:
            conn.close()

    @app.post("/approve")
    def do_approve():
        import urllib.parse as up
        key = (request.form.get("key") or "").strip()
        ok, detail = approve_pair(key)
        return redirect(url_for("page_pairs") + "?flash="
                        + up.quote("Approved." if ok else detail))

    @app.post("/revoke")
    def do_revoke():
        key = (request.form.get("key") or "").strip()
        if key:
            revoke_pair(key)
        return redirect(url_for("page_pairs"))

    @app.route("/scans")
    def page_scans():
        conn = connect()
        try:
            init_db(conn)
            return render_template("scans.html", **ctx(
                "scans", rows=q("SELECT * FROM scans ORDER BY id DESC LIMIT 200",
                                (), conn)))
        finally:
            conn.close()

    @app.route("/learn")
    def page_learn():
        return render_template("learn.html", **ctx("learn"))

    @app.route("/logs")
    def page_logs():
        conn = connect()
        try:
            init_db(conn)
            level = request.args.get("level", "").strip().upper()
            term = request.args.get("qq", "").strip()
            sql, args = "SELECT * FROM audit_log WHERE 1=1", []
            if level in ("INFO", "WARN", "ERROR"):
                sql += " AND level=?"
                args.append(level)
            if term:
                sql += " AND (message LIKE ? OR source LIKE ?)"
                args += [f"%{term}%"] * 2
            sql += " ORDER BY id DESC LIMIT 300"
            return render_template("logs.html", **ctx(
                "logs", rows=q(sql, tuple(args), conn), f_level=level, f_q=term,
                dbfile=os.path.abspath(db_path())))
        finally:
            conn.close()

    @app.route("/export/<fmt>")
    def export(fmt):
        try:
            sid = int(request.args.get("scan", "") or 0) or None
        except ValueError:
            sid = None
        fmt = fmt.lower()
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
        if fmt == "json":
            body, mime = export_json(sid), "application/json"
        elif fmt == "csv":
            body, mime = export_csv(sid), "text/csv"
        elif fmt == "html":
            body, mime = export_html(sid), "text/html"
        else:
            return Response("Unsupported format. Use json, csv or html.", 400,
                            mimetype="text/plain")
        log_event("INFO", "export", f"Exported the report as {fmt.upper()}", sid)
        return Response(body, mimetype=mime, headers={
            "Content-Disposition": f'attachment; filename="arpcheck-{stamp}.{fmt}"'})

    @app.route("/api/summary")
    def api_summary():
        sid = latest_scan_id()
        if not sid:
            return jsonify({"error": "no checks yet"}), 404
        s = scan_summary(sid)
        return jsonify({"tool": APP_NAME, "version": VERSION, "read_only": True,
                        "arp_has_no_authentication": True,
                        "cannot_identify_the_legitimate_reply": True,
                        "sees_only_this_segment": True,
                        "disclaimer": DISCLAIMER_SHORT,
                        "scan": {k: v for k, v in s.items() if k != "payload"}})

    @app.errorhandler(404)
    def nf(_e):
        return Response("404 - page not found. Valid pages: / /pairs /scans /learn /logs",
                        404, mimetype="text/plain")

    return app


def serve(host: str, port: int, debug: bool = False):
    app = build_app()
    init_db()
    log_event("INFO", "web", f"Web app started on http://{host}:{port}")
    print(f"\n  {APP_NAME} v{VERSION} - by {AUTHOR}")
    print(f"  {'-' * 66}")
    print(f"  Web app : http://{'127.0.0.1' if host == '0.0.0.0' else host}:{port}")
    print(f"  Database: {os.path.abspath(db_path())}")
    if not is_root():
        print("  NOTE    : not running as root, so verification cannot send ARP\n"
              "            requests. The consistency checks need no privileges.")
    if host == "0.0.0.0":
        print("  WARNING : bound to 0.0.0.0 - anyone who reaches this UI can make this\n"
              "            machine broadcast ARP traffic. Use 127.0.0.1.")
    print(f"  {textwrap.fill(DISCLAIMER_SHORT, 66, subsequent_indent='  ')}")
    print(f"  {'-' * 66}\n  Press Ctrl+C to stop.\n")
    app.run(host=host, port=port, debug=debug, use_reloader=False)


# =============================================================================
# SECTION 11 - Command line interface
# =============================================================================

def line(char="-", n=78):
    print(char * n)


def banner():
    print(f"\n{APP_NAME} v{VERSION}  |  {AUTHOR}")
    line()
    print(textwrap.fill(DISCLAIMER_SHORT, 78))
    line()


def _print_findings(rows, limit=None, quiet=False):
    shown = [f for f in rows if not (quiet and f["severity"] == "info")]
    shown = shown[:limit] if limit else shown
    for f in shown:
        print(f"\n  [{f['severity'].upper():^8}] {f['title']}")
        for l in textwrap.wrap(f["description"], 70):
            print(f"      {l}")
        if f.get("evidence"):
            for l in str(f["evidence"]).splitlines()[:10]:
                for w in textwrap.wrap(l, 70) or [""]:
                    print(f"      {w}")
        if f.get("advice"):
            for l in textwrap.wrap("what to make of it: " + f["advice"], 70):
                print(f"      {l}")


def _report(res, a):
    arp, gw = res["arp"], res["gateway"]
    print(f"Source : {(arp.data or {}).get('source')}")
    if arp.detail:
        for l in textwrap.wrap(arp.detail, 74):
            print(f"         {l}")
    print(f"Gateway: {gw.get('ip') or 'none'} via {gw.get('interface') or '?'}")
    nets = ", ".join(f"{k} {v['network']}" for k, v in res["interfaces"].items()
                     if v.get("network"))
    print(f"Subnets: {nets or 'none found'}")
    print(f"Time   : {res['elapsed_ms']} ms")
    line("=")
    entries = res["entries"]
    print(f"  {len(entries)} ENTRY(IES)   -   {res['band'].upper()}")
    if res["verify"] and res["verify"].status == "ok":
        vr = res["verify"].data["results"]
        print(f"  verified {len(vr)}: "
              f"{sum(1 for v in vr.values() if v['state'] == 'valid')} match, "
              f"{sum(1 for v in vr.values() if v['state'] == 'stale')} differ, "
              f"{sum(1 for v in vr.values() if v['state'] == 'conflict')} conflict, "
              f"{sum(1 for v in vr.values() if v['state'] == 'silent')} silent")
    else:
        print("  not verified against the network")
    line("=")
    if entries:
        vres = (res["verify"].data or {}).get("results", {}) if res["verify"] else {}
        print(f"  {'IP':<17} {'HARDWARE':<19} {'IFACE':<8} {'FLAGS':<6} WIRE")
        line()
        for e in entries[:30]:
            probs = [p for p in res["validation"]["per_entry"].get(e["ip"], [])
                     if p["severity"] != "info"]
            flags = ("C" if e["complete"] else "-") + ("S" if e["permanent"] else "-") \
                + ("P" if e["published"] else "-")
            v = vres.get(e["ip"]) or {}
            wire = {"valid": "matches", "stale": "DIFFERENT", "conflict": "TWO ANSWERS",
                    "silent": "silent"}.get(v.get("state"), "-")
            mark = "!" if probs else (" " if not v.get("state") in ("stale", "conflict")
                                      else "!")
            gwmark = "*" if gw.get("ip") == e["ip"] else " "
            print(f" {mark}{gwmark}{e['ip']:<17} {e['mac']:<19} {e['device'][:7]:<8} "
                  f"{flags:<6} {wire}")
            if a.verbose:
                for p in probs:
                    print(f"      -> {p['detail']}")
        if len(entries) > 30:
            print(f"  ... and {len(entries) - 30} more")
        line()
        print("  * is the gateway, ! has something worth reading below")
        print("  flags: C complete, S static, P published")
        line()
    _print_findings(res["findings"], a.show, a.quiet)
    line()
    print(textwrap.fill("  " + NO_AUTHENTICATION, 78))
    line()


def cmd_check(a):
    banner()
    res = run_check(do_verify=False, note=a.note or "")
    _report(res, a)
    return _exit_code(a, res)


def cmd_verify(a):
    banner()
    print(textwrap.fill(
        "This BROADCASTS an ARP request for every cached address. That is ordinary traffic - "
        "every machine does it constantly - but it puts this machine's address in front of "
        "everything on the segment and will populate other machines' caches. Only run it on "
        "a network you are responsible for.", 78))
    line()
    if not is_root():
        print("  NOTE: sending ARP requests needs root. Without it verification cannot")
        print("        run, and the report will say so rather than appearing clean.")
        line()
    if not a.yes:
        try:
            answer = input("  Send the requests? [y/N] ").strip().lower()
        except EOFError:
            answer = ""
        if answer not in ("y", "yes"):
            print("  Not sent. Use 'check' for the consistency checks, which transmit "
                  "nothing.")
            return 0
    only = a.ip or None
    res = run_check(do_verify=True, per_target_wait=a.wait,
                    only_ips=[only] if only else None, note=a.note or "",
                    progress=(lambda ip: print(f"  asking {ip} ...")) if a.verbose
                    else None)
    _report(res, a)
    return _exit_code(a, res)


def cmd_watch(a):
    banner()
    print(f"Checking every {a.interval:.0f}s"
          + (f", {a.count} times" if a.count else " until Ctrl+C") + ".")
    print("Consistency checks only - nothing is transmitted. Only changes are printed.\n")
    seen: set = set()
    n = 0
    try:
        while True:
            n += 1
            res = run_check(do_verify=False, note="watch")
            stamp = datetime.now().strftime("%H:%M:%S")
            pairs = {f"{e['ip']}|{e['mac']}" for e in res["entries"] if e["complete"]}
            new = pairs - seen
            alerts = [f for f in res["findings"]
                      if f["severity"] in ("critical", "high")]
            if new or alerts:
                print(f"  {stamp}  #{res['id']}  {len(res['entries'])} entry(ies)")
                for k in sorted(new):
                    ip, mac = k.split("|")
                    gw = " (GATEWAY)" if res["gateway"].get("ip") == ip else ""
                    print(f"      new pair  {ip} -> {mac}{gw}")
                for f in alerts:
                    print(f"   !! [{f['severity'].upper()}] {f['title']}")
            elif not a.quiet:
                print(f"  {stamp}  #{res['id']}  {len(res['entries'])} entry(ies), "
                      f"nothing new")
            seen |= pairs
            if a.count and n >= a.count:
                break
            time.sleep(a.interval)
    except KeyboardInterrupt:
        print("\nStopped.")
    line()
    print(f"  {n} check(s), {len(seen)} distinct pair(s) seen.")
    line()
    return 0


def _exit_code(a, res):
    counts = res["counts"]
    if a.fail_on_critical and counts["critical"]:
        print(f"  Exiting non-zero: {counts['critical']} critical finding(s).")
        return 2
    if a.fail_over is not None and res["score"] > a.fail_over:
        print(f"  Exiting non-zero: score {res['score']} is above --fail-over "
              f"{a.fail_over}")
        return 2
    return 0


def cmd_pairs(a):
    rows = q("SELECT * FROM pairs ORDER BY approved DESC, ip LIMIT ?", (a.limit,))
    if not rows:
        print("No pairs recorded yet. Run:  check")
        return 0
    print(f"  {'IP':<17} {'HARDWARE':<19} {'SEEN':>5}  {'APPROVED':<9} LABEL")
    line()
    for r in rows:
        print(f"  {r['ip']:<17} {r['mac']:<19} {r['times_seen']:>5}  "
              f"{('yes' if r['approved'] else 'no'):<9} {r['label'] or ''}")
    line()
    unapproved = [r for r in rows if not r["approved"]]
    if unapproved:
        print(f"  {len(unapproved)} not approved. Approve one with:")
        print(f"    python3 {os.path.basename(__file__)} approve {unapproved[0]['ip']}")
        line()
    return 0


def cmd_approve(a):
    ok, detail = approve_pair(a.target, a.label or "", a.note or "")
    if not ok:
        print(detail)
        return 1
    print(f"Approved {detail}")
    print()
    print(textwrap.fill(
        "It will no longer be reported. This is the right thing to do for a router that "
        "legitimately answers for several addresses - approving it means a genuinely new "
        "duplicate stands out.", 78))
    return 0


def cmd_revoke(a):
    n = revoke_pair(a.target)
    print(f"Revoked {n} approval(s)." if n else f"'{a.target}' was not approved.")
    return 0


def cmd_learn(_a):
    banner()
    print(textwrap.dedent("""\
        ARP HAS NO AUTHENTICATION

          A machine broadcasts "who has this address" and believes whichever
          answer arrives. There is no signature, no challenge, and nothing to
          check the reply against. The last answer wins.

          That is not a bug in any implementation - it is how the protocol was
          designed in 1982, and everything below follows from it. It also means
          this tool cannot tell you which reply is legitimate, only that something
          disagrees.

        TWO DIFFERENT QUESTIONS

          IS THE ENTRY INTERNALLY CONSISTENT?
            An address outside the interface's own subnet cannot be reached by ARP
            at all. A broadcast or multicast hardware address in a unicast entry is
            meaningless. One hardware address claiming several IP addresses is
            either proxy ARP or somebody answering for addresses that are not
            theirs.

            None of this touches the network. It is arithmetic on the cache, the
            interface addresses and the routing table - so it needs no privileges
            and nothing on the wire can fool it.

          IS THE ENTRY STILL TRUE?
            A cached entry is a claim that nothing revalidates until it ages out.
            Verification re-asks and compares. One different answer means the cache
            is stale. TWO ANSWERS to one question means two machines claim one
            address, which is what spoofing looks like from here.

        THE GATEWAY IS THE ENTRY WORTH STEALING

          Everything leaving the subnet is sent to the gateway's hardware address.
          An attacker who answers for the gateway sees all of it, and needs to
          convince only one machine. That is why a hardware address covering both
          the gateway and other hosts is the highest severity here.

          A STATIC ENTRY FOR THE GATEWAY is a cheap and genuinely effective
          defence, because a static entry does not get overwritten by a reply.

        A DUPLICATE IS USUALLY NOT AN ATTACK

          One hardware address holding several IP addresses is completely normal
          for a router doing proxy ARP, a firewall with secondary addresses, or a
          virtualisation host. What makes it interesting is where it appears, and
          above all whether it covers the gateway. Approve the ones you recognise
          so a genuinely new duplicate stands out.

        FLAGS WORTH UNDERSTANDING

          complete    a reply was received
          incomplete  the request went out and nothing answered. Ordinary for an
                      address not in use - though many at once is the trace a
                      subnet sweep leaves in the cache of the machine sweeping
          static      configured by hand, never ages out. A good defence, and also
                      a wrong entry that stays wrong until removed
          published   this machine answers ARP for an address that is not its own.
                      Deliberate on a router, worth confirming anywhere else

        WHAT THIS CANNOT SEE

          Only this machine's cache and this machine's segment. ARP DOES NOT CROSS
          A ROUTER, so nothing beyond the gateway appears here at all. The cache
          holds only what this machine has recently talked to, so an absent device
          is not necessarily absent from the network.

          During verification, silence means the device did not answer - it may be
          off, asleep or filtering. That does not mean the cached entry is wrong,
          and it does not mean it is right. A confirmation is a confirmation at one
          moment only: an ARP cache can be overwritten at any time by anything on
          the segment.
        """))
    line()


def cmd_scans(a):
    rows = q("SELECT * FROM scans ORDER BY id DESC LIMIT ?", (a.limit,))
    if not rows:
        print("Nothing checked yet.")
        return 0
    print(f"{'ID':>4}  {'WHEN (UTC)':<20} {'ENT':>4} {'DUP':>4} {'CONF':>5} {'SCORE':>6} "
          f"{'VER':>4}  VERDICT")
    line()
    for r in rows:
        print(f"{r['id']:>4}  {r['ts'][:19].replace('T', ' '):<20} {r['entries']:>4} "
              f"{r['duplicate_macs']:>4} {r['conflicts']:>5} {r['score']:>6} "
              f"{('yes' if r['verified'] else 'no'):>4}  {r['band'] or ''}")
    return 0


def cmd_export(a):
    sid = a.scan or latest_scan_id()
    if not sid:
        print("Nothing to export yet.")
        return 1
    fmt = a.format.lower()
    body = {"json": export_json, "csv": export_csv, "html": export_html}[fmt](sid)
    out = a.out or f"arpcheck-{datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S')}.{fmt}"
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(body)
    log_event("INFO", "export", f"Exported check #{sid} as {fmt.upper()} to {out}", sid)
    print(f"Wrote {out} ({len(body):,} bytes)")
    return 0


def cmd_logs(a):
    sql, args = "SELECT * FROM audit_log WHERE 1=1", []
    if a.level:
        sql += " AND level=?"
        args.append(a.level.upper())
    sql += " ORDER BY id DESC LIMIT ?"
    args.append(a.limit)
    rows = q(sql, tuple(args))
    if not rows:
        print("No log entries.")
        return 0
    for e in reversed(rows):
        print(f"{e['ts'][:19].replace('T', ' ')}  {e['level']:<5} {e['source']:<11} "
              f"{e['message']}")
    return 0


def cmd_purge(a):
    conn = connect()
    try:
        if a.all:
            for t in ("findings", "observations", "scans", "audit_log"):
                conn.execute(f"DELETE FROM {t}")
            if a.pairs:
                conn.execute("DELETE FROM pairs")
            conn.commit()
            print("All checks, observations and logs deleted."
                  + (" The pair list was cleared too." if a.pairs
                     else " The pair list and approvals were kept."))
            return 0
        rows = q("SELECT id FROM scans ORDER BY id DESC", (), conn)
        drop = [r["id"] for r in rows[a.keep:]]
        for sid in drop:
            for t in ("findings", "observations"):
                conn.execute(f"DELETE FROM {t} WHERE scan_id=?", (sid,))
            conn.execute("DELETE FROM scans WHERE id=?", (sid,))
        conn.commit()
        print(f"Purged {len(drop)} check(s); kept the newest {a.keep}.")
        return 0
    finally:
        conn.close()


def cmd_serve(a):
    serve(a.host, a.port, a.debug)


def cmd_version(_a):
    banner()
    arp = read_arp_table()
    print(f"  Python     : {platform.python_version()} ({sys.platform})")
    print(f"  Flask      : {'yes' if HAVE_FLASK else 'NOT INSTALLED - web app unavailable'}")
    print(f"  Privileges : {'root' if is_root() else 'unprivileged - verification cannot send'}")
    print(f"  ARP source : {(arp.data or {}).get('source')} ({arp.status})")
    print(f"  Entries    : {len((arp.data or {}).get('entries', []))}")
    gw = default_gateway()
    print(f"  Gateway    : {gw.get('ip') or gw.get('error')}")
    for name, i in interface_networks().items():
        if i.get("network"):
            print(f"    {name:<8} {i['address']}/{i['netmask']}  {i['mac']}")
    print(f"  Database   : {os.path.abspath(db_path())}")
    print(f"  GitHub     : {GITHUB}")
    line()
    print(DISCLAIMER_LONG)
    line()


# =============================================================================
# SECTION 12 - Self test
# =============================================================================

def _entry(ip, mac, device="eth0", complete=True, permanent=False, published=False):
    d = describe_mac(mac)
    return {"ip": ip, "mac": d["mac"], "device": device,
            "flags": (ATF_COM if complete else 0) | (ATF_PERM if permanent else 0)
            | (ATF_PUBL if published else 0),
            "flags_hex": "0x2", "complete": complete, "permanent": permanent,
            "published": published, "hw_type": 1, "hw_type_name": "Ethernet",
            "mask": "*", "vendor": d["vendor"], "virtual": d["virtual"],
            "locally_administered": d["locally_administered"],
            "multicast_mac": d["multicast"], "broadcast_mac": d["broadcast"],
            "null_mac": d["null"], "valid_mac": d["valid"]}


def cmd_selftest(_a=None) -> int:
    import tempfile
    passed, failed, skipped = [], [], []

    def check(name, cond, detail=""):
        (passed if cond else failed).append(name)
        print(f"  [{'PASS' if cond else 'FAIL'}] {name}"
              f"{'  <- ' + str(detail) if detail and not cond else ''}")

    def skip(name, why):
        skipped.append(name)
        print(f"  [SKIP] {name}  ({why})")

    banner()
    print("SELF TEST - validation against fixtures, collectors against this machine.\n")
    original = db_path()
    tmp = tempfile.mkdtemp(prefix="arpcheck-selftest-")
    set_db_path(os.path.join(tmp, "selftest.db"))
    IFACES = {"eth0": {"name": "eth0", "address": "192.0.2.2",
                       "netmask": "255.255.255.0", "network": "192.0.2.0/24",
                       "mac": "aa:bb:cc:00:00:02", "error": None}}
    GW = {"ip": "192.0.2.1", "interface": "eth0", "error": None}
    try:
        print(" Hardware addresses")
        check("an address normalises",
              normalise_mac("AA-BB-CC-DD-EE-FF") == "aa:bb:cc:dd:ee:ff")
        check("a bare hex string normalises",
              normalise_mac("aabbccddeeff") == "aa:bb:cc:dd:ee:ff")
        check("broadcast is identified", describe_mac(BROADCAST_MAC)["broadcast"])
        check("all zeroes is identified", describe_mac(NULL_MAC)["null"])
        check("the multicast bit is read", describe_mac("01:00:5e:00:00:01")["multicast"])
        check("the locally-administered bit is read",
              describe_mac("02:00:00:00:00:01")["locally_administered"])
        check("a known vendor is named",
              describe_mac("b8:27:eb:11:22:33")["vendor"] == "Raspberry Pi")
        check("a virtualisation prefix is identified",
              describe_mac("52:54:00:12:34:56")["virtual"])
        check("nonsense is rejected", not describe_mac("not a mac")["valid"])

        print("\n Reading the cache")
        arp = read_arp_table()
        check(f"the ARP cache is read ({arp.status})",
              arp.status in ("ok", "partial", "unavailable"))
        if arp.data and arp.data["entries"]:
            e = arp.data["entries"][0]
            check("every entry has an address, a MAC and a device",
                  all(x["ip"] and x["mac"] and x["device"] for x in arp.data["entries"]))
            check("flags are decoded into booleans",
                  isinstance(e["complete"], bool) and isinstance(e["permanent"], bool))
        ifaces = interface_networks()
        check("interface subnets are read",
              any(i.get("network") for i in ifaces.values()), list(ifaces))
        gw = default_gateway()
        check("the gateway is found or the absence explained",
              gw.get("ip") or gw.get("error"), gw)

        print("\n Validating one entry")
        good = _entry("192.0.2.50", "b8:27:eb:11:22:33")
        probs = validate_entry(good, IFACES, GW)
        check("a well-formed in-subnet entry has no problems",
              not [p for p in probs if p["severity"] != "info"], probs)
        probs = validate_entry(_entry("10.9.9.9", "b8:27:eb:11:22:33"), IFACES, GW)
        check("an address outside the interface's subnet is HIGH",
              any(p["kind"] == "off_subnet" and p["severity"] == "high" for p in probs),
              probs)
        check("and the reason names ARP's scope",
              any("only works within a subnet" in p["why"] for p in probs))
        probs = validate_entry(_entry("192.0.2.50", BROADCAST_MAC), IFACES, GW)
        check("the broadcast hardware address is HIGH",
              any(p["kind"] == "broadcast_mac" and p["severity"] == "high" for p in probs))
        probs = validate_entry(_entry("192.0.2.50", "01:00:5e:00:00:01"), IFACES, GW)
        check("a multicast hardware address is HIGH",
              any(p["kind"] == "multicast_mac" for p in probs), probs)
        probs = validate_entry(_entry("192.0.2.2", "b8:27:eb:11:22:33"), IFACES, GW)
        check("an entry for this machine's own address is reported",
              any(p["kind"] == "own_address" for p in probs), probs)
        probs = validate_entry(_entry("192.0.2.50", "b8:27:eb:11:22:33", device="zz9"),
                               IFACES, GW)
        check("an entry naming an interface that does not exist is reported",
              any(p["kind"] == "unknown_device" for p in probs), probs)
        probs = validate_entry(_entry("224.0.0.1", "01:00:5e:00:00:01"), IFACES, GW)
        check("a multicast IP address is reported",
              any(p["kind"] == "multicast_ip" for p in probs), probs)
        probs = validate_entry(_entry("192.0.2.1", "b8:27:eb:11:22:33"), IFACES, GW)
        check("the gateway is identified as such",
              any(p["kind"] == "is_gateway" for p in probs))
        probs = validate_entry(_entry("192.0.2.9", NULL_MAC, complete=False), IFACES, GW)
        check("an incomplete entry is INFO, not a problem",
              all(p["severity"] == "info" for p in probs
                  if p["kind"] in ("incomplete", "null_mac")), probs)
        probs = validate_entry(_entry("192.0.2.60", "b8:27:eb:11:22:33", published=True),
                               IFACES, GW)
        check("a published entry is reported as proxy ARP",
              any(p["kind"] == "published" for p in probs))
        probs = validate_entry(_entry("192.0.2.1", "b8:27:eb:11:22:33", permanent=True),
                               IFACES, GW)
        check("a static entry is INFO and its trade-off explained",
              any(p["kind"] == "static" and "stays wrong" in p["why"] for p in probs))

        print("\n Validating the table as a whole")
        table = [_entry("192.0.2.1", "de:ad:be:ef:00:01"),
                 _entry("192.0.2.50", "de:ad:be:ef:00:01"),
                 _entry("192.0.2.51", "b8:27:eb:11:22:33")]
        v = validate_table(table, IFACES, GW)
        check("one MAC on several IPs is detected",
              len(v["duplicate_macs"]) == 1
              and v["duplicate_macs"][0]["count"] == 2, v["duplicate_macs"])
        check("the gateway entry is found",
              v["gateway_entry"] and v["gateway_entry"]["ip"] == "192.0.2.1")
        check("and the addresses sharing the gateway's MAC are listed",
              v["gateway_shared_with"] == ["192.0.2.50"], v["gateway_shared_with"])
        clean = [_entry("192.0.2.1", "de:ad:be:ef:00:01"),
                 _entry("192.0.2.50", "b8:27:eb:11:22:33")]
        v2 = validate_table(clean, IFACES, GW)
        check("a clean table produces no duplicates",
              not v2["duplicate_macs"] and not v2["gateway_shared_with"])
        dup_ip = [_entry("192.0.2.7", "aa:aa:aa:aa:aa:aa", device="eth0"),
                  _entry("192.0.2.7", "bb:bb:bb:bb:bb:bb", device="eth1")]
        v3 = validate_table(dup_ip, IFACES, GW)
        check("one IP with two MACs is detected",
              len(v3["duplicate_ips"]) == 1, v3["duplicate_ips"])

        print("\n Findings")
        src = Result("arp")
        src.data = {"entries": table, "source": "fixture"}
        f = analyse(src, v, None, IFACES, GW, {})
        check("the gateway sharing its MAC is CRITICAL",
              any(x["severity"] == "critical" and "gateway" in x["title"].lower()
                  for x in f), [x["title"] for x in f])
        check("and the advice offers proxy ARP as the innocent explanation",
              any("proxy ARP" in x.get("advice", "") for x in f))
        check("and says to confirm before concluding",
              any("before concluding" in x.get("advice", "") for x in f))
        src.data["entries"] = clean
        f = analyse(src, v2, None, IFACES, GW, {})
        check("a clean table raises nothing above informational",
              not any(x["severity"] in ("critical", "high") for x in f),
              [x["title"] for x in f])
        check("and it still says entries were not verified",
              any("NOT verified" in x["title"] for x in f))
        key = f"192.0.2.1|de:ad:be:ef:00:01"
        f = analyse(src, v, None, IFACES, GW, {key: {"approved": True}})
        src.data["entries"] = table
        check("approving the gateway pair silences the critical finding",
              not any(x["severity"] == "critical" for x in
                      analyse(src, v, None, IFACES, GW, {key: {"approved": True}})),
              "a router legitimately doing proxy ARP should be approvable")
        many_incomplete = [_entry(f"192.0.2.{i}", NULL_MAC, complete=False)
                           for i in range(60, 100)]
        vmi = validate_table(many_incomplete, IFACES, GW)
        src.data["entries"] = many_incomplete
        f = analyse(src, vmi, None, IFACES, GW, {})
        check("many incomplete entries are reported as a possible sweep",
              any("sweep" in x.get("advice", "") for x in f), [x["title"] for x in f])
        empty = Result("arp")
        empty.data = {"entries": [], "source": "fixture"}
        f = analyse(empty, {"per_entry": {}, "duplicate_macs": [], "duplicate_ips": [],
                            "gateway_entry": None, "gateway_shared_with": []},
                    None, IFACES, GW, {})
        check("an empty cache is explained rather than treated as clean",
              any("cache is empty" in x["title"] for x in f)
              and any("not the same as nothing being there" in x.get("advice", "")
                      for x in f), [x["title"] for x in f])

        print("\n ARP frames")
        frame = build_arp_request("aa:bb:cc:dd:ee:ff", "192.0.2.2", "192.0.2.1")
        p = parse_arp_frame(frame)
        check("a request we build parses back",
              p and p["op"] == ARP_REQUEST, p)
        check("it carries our address", p["sender_ip"] == "192.0.2.2")
        check("and asks for the right target", p["target_ip"] == "192.0.2.1")
        check("it is broadcast", frame[:6] == b"\xff" * 6)
        check("a non-ARP frame is rejected", parse_arp_frame(b"\x00" * 60) is None)
        check("a truncated frame is rejected", parse_arp_frame(b"\x00" * 20) is None)

        print("\n Verification verdicts")
        e = _entry("192.0.2.1", "aa:bb:cc:00:00:01")
        r_ = _classify_verification(e, [{"sender_mac": "aa:bb:cc:00:00:01",
                                         "eth_src": "aa:bb:cc:00:00:01",
                                         "sender_ip": "192.0.2.1"}])
        check("a matching reply is 'valid'", r_["state"] == "valid", r_)
        r_ = _classify_verification(e, [{"sender_mac": "de:ad:be:ef:00:01",
                                         "eth_src": "de:ad:be:ef:00:01",
                                         "sender_ip": "192.0.2.1"}])
        check("a different reply is 'stale'", r_["state"] == "stale")
        check("and both addresses are shown",
              "aa:bb:cc:00:00:01" in r_["detail"] and "de:ad:be:ef:00:01" in r_["detail"])
        r_ = _classify_verification(e, [
            {"sender_mac": "aa:bb:cc:00:00:01", "eth_src": "aa:bb:cc:00:00:01",
             "sender_ip": "192.0.2.1"},
            {"sender_mac": "de:ad:be:ef:00:01", "eth_src": "de:ad:be:ef:00:01",
             "sender_ip": "192.0.2.1"}])
        check("two different replies is 'conflict'", r_["state"] == "conflict")
        r_ = _classify_verification(e, [])
        check("no reply is 'silent', not 'wrong'", r_["state"] == "silent", r_)
        check("and silence is explained as ambiguous",
              "does not mean" in r_["detail"])
        r_ = _classify_verification(e, [{"sender_mac": "aa:bb:cc:00:00:01",
                                         "eth_src": "de:ad:be:ef:99:99",
                                         "sender_ip": "192.0.2.1"}])
        check("a frame whose ethernet source disagrees with the payload is flagged",
              r_.get("frame_mismatch"), r_)

        print("\n Running for real")
        res = run_check(do_verify=False)
        check("a check completes on this machine", res["id"] > 0)
        check("it did not transmit", res["verify"] is None)
        check("every finding carries advice",
              all(f.get("advice") for f in res["findings"]),
              [f["title"] for f in res["findings"] if not f.get("advice")])
        check("a real machine produces no critical findings",
              not any(f["severity"] == "critical" for f in res["findings"]),
              [f["title"] for f in res["findings"] if f["severity"] == "critical"])

        print("\n Persistence")
        s = scan_summary(res["id"])
        check("a check is stored", s and s["id"] == res["id"])
        check("observations are stored per entry",
              q1("SELECT COUNT(*) c FROM observations WHERE scan_id=?",
                 (res["id"],))["c"] == len(res["entries"]))
        check("findings are stored",
              q1("SELECT COUNT(*) c FROM findings WHERE scan_id=?",
                 (res["id"],))["c"] == len(res["findings"]))
        run_check(do_verify=False)
        if res["entries"]:
            check("seeing a pair twice increments rather than duplicating",
                  all(r["times_seen"] >= 2 for r in q("SELECT * FROM pairs", ())),
                  [dict(r) for r in q("SELECT ip, times_seen FROM pairs", ())])
            ip = res["entries"][0]["ip"]
            ok, k = approve_pair(ip, "test")
            check("a pair can be approved by its address", ok, k)
            check("approval is recorded", baseline_map()[k]["approved"])
            check("approval can be revoked",
                  revoke_pair(ip) >= 1 and not baseline_map()[k]["approved"])
        ok, why = approve_pair("203.0.113.99")
        check("approving something never seen is refused with a reason",
              not ok and "has not been seen" in why, why)

        print("\n Charts")
        tbl = svg_table(table, v, {}, GW, {})
        check("a row is drawn per entry", tbl.count("<rect") >= len(table))
        check("the gateway row is marked", "(gateway)" in tbl)
        check("the table with no entries says so", "cache is empty" in svg_table(
            [], {}, {}, GW, {}))
        mm = svg_mac_map(v, GW)
        check("the shared-MAC map draws the fan", mm.count("<rect") > 1)
        check("and marks the gateway inside it", "GATEWAY" in mm)
        check("the map says so when there is nothing to draw",
              "nothing to draw" in svg_mac_map(v2, GW))
        check("pie renders slices",
              svg_pie([("a", 2, "#fff"), ("b", 1, "#000")]).count("<path") == 2)
        check("charts guard against empty input",
              all("nothing to show" in x or "nothing to draw" in x or "empty" in x
                  for x in (svg_pie([]), svg_bar([]), svg_table([], {}, {}, GW, {}),
                            svg_mac_map({"duplicate_macs": []}, GW))))

        print("\n Exports")
        j = json.loads(export_json(res["id"]))
        check("JSON export carries the disclaimer",
              "NO AUTHENTICATION" in j["disclaimer"].upper())
        check("JSON export says ARP has no authentication",
              "no authentication" in j["arp_has_no_authentication"])
        check("JSON export says a duplicate is usually not an attack",
              "normal for a router" in j["a_duplicate_is_usually_not_an_attack"])
        check("JSON export lists the limitations", len(j["limitations"]) >= 7)
        check("JSON export says ARP does not cross a router",
              any("does not cross a router" in x for x in j["limitations"]))
        check("JSON export says silence is ambiguous",
              any("not that the cached entry is wrong" in x for x in j["limitations"]))
        c_ = export_csv(res["id"])
        check("CSV export has sections", c_.count("##") >= 3)
        check("CSV says which reply is legitimate cannot be known",
              any("no authentication" in l.lower() for l in c_.splitlines()[:6]))
        h = export_html(res["id"])
        check("HTML export is a complete document",
              h.startswith("<!doctype html") and h.rstrip().endswith("</html>"))
        check("HTML export contains charts and the author", "<svg" in h and AUTHOR in h)

        print("\n Web application")
        if not HAVE_FLASK:
            check("Flask installed", False, "pip install flask")
        else:
            app = build_app()
            app.config["TESTING"] = True
            cl = app.test_client()
            for path, must in (("/", "Overview"), ("/pairs", "Address pairs"),
                               ("/scans", "Checks"), ("/learn", "no authentication"),
                               ("/logs", "Logs")):
                r_ = cl.get(path)
                body = r_.get_data(as_text=True)
                check(f"page {path} renders",
                      r_.status_code == 200 and must.lower() in body.lower(),
                      r_.status_code)
            check("every page says ARP has no authentication",
                  "no authentication" in cl.get("/").get_data(as_text=True).lower())
            check("the learn page explains the two questions",
                  "internally consistent" in cl.get("/learn").get_data(as_text=True))
            check("the learn page recommends a static gateway entry",
                  "static entry" in cl.get("/learn").get_data(as_text=True).lower())
            check("the verify button warns before transmitting",
                  "BROADCASTS" in cl.get("/").get_data(as_text=True))
            r_ = cl.post("/check")
            check("a check runs from the web", r_.status_code == 302)
            if res["entries"]:
                k = f"{res['entries'][0]['ip']}|{res['entries'][0]['mac']}"
                r_ = cl.post("/approve", data={"key": k})
                check("approving from the web works",
                      r_.status_code == 302 and baseline_map()[k]["approved"])
                r_ = cl.post("/revoke", data={"key": k})
                check("revoking from the web works",
                      r_.status_code == 302 and not baseline_map()[k]["approved"])
            for fmt, ctype in (("json", "application/json"), ("csv", "text/csv"),
                               ("html", "text/html")):
                r_ = cl.get(f"/export/{fmt}?scan={res['id']}")
                check(f"export /{fmt} downloads",
                      r_.status_code == 200 and ctype in r_.headers["Content-Type"]
                      and "attachment" in r_.headers.get("Content-Disposition", ""))
            check("bad export format is rejected", cl.get("/export/exe").status_code == 400)
            check("unknown route returns a helpful 404", cl.get("/nope").status_code == 404)
            api = cl.get("/api/summary").get_json()
            check("the api declares it is read-only", api["read_only"] is True)
            check("the api declares it cannot identify the legitimate reply",
                  api["cannot_identify_the_legitimate_reply"] is True)

        print("\n It never alters the cache")
        mod = sys.modules[__name__]
        import inspect
        writers = [n for n in dir(mod)
                   if n.startswith(("set_arp", "add_arp", "delete_arp", "del_arp",
                                    "flush_arp", "poison"))]
        check("no function exists to add, delete or alter an ARP entry", not writers,
              writers)
        consts = {n for n in dir(mod) if n.isupper()}
        check("the ioctl to SET an ARP entry is not defined",
              "SIOCSARP" not in consts and "SIOCDARP" not in consts, sorted(consts))
        src_check = inspect.getsource(read_arp_table)
        check("reading the cache transmits nothing",
              "send" not in src_check and "sendto" not in src_check)
        check("only verification transmits",
              "sock.send" in inspect.getsource(verify_entries))

        print("\n Retention")
        cmd_purge(argparse.Namespace(all=False, keep=1, pairs=False))
        check("purge keeps exactly the newest check",
              q1("SELECT COUNT(*) c FROM scans", ())["c"] == 1)
        check("purge removes orphaned observations and findings",
              all(q1(f"SELECT COUNT(*) c FROM {t} WHERE scan_id NOT IN "
                     f"(SELECT id FROM scans)", ())["c"] == 0
                  for t in ("observations", "findings")))
        cmd_purge(argparse.Namespace(all=True, keep=1, pairs=False))
        check("purge --all clears the checks",
              q1("SELECT COUNT(*) c FROM scans", ())["c"] == 0)
        if res["entries"]:
            check("the pair list survives by default",
                  q1("SELECT COUNT(*) c FROM pairs", ())["c"] > 0)
        cmd_purge(argparse.Namespace(all=True, keep=1, pairs=True))
        check("purge --all --pairs clears it too",
              q1("SELECT COUNT(*) c FROM pairs", ())["c"] == 0)
    finally:
        set_db_path(original)
        shutil.rmtree(tmp, ignore_errors=True)

    line("=")
    print(f"  {len(passed)} passed, {len(failed)} failed"
          + (f", {len(skipped)} skipped" if skipped else ""))
    if failed:
        print("  Failed: " + ", ".join(failed))
    if skipped:
        print("  Skipped: " + ", ".join(skipped))
    if not failed:
        print("  All checks passed. No ARP request was broadcast, no entry was altered,\n"
              "  and the temporary database has been removed.")
    line("=")
    return 0 if not failed else 1


# =============================================================================
# SECTION 13 - Entry point
# =============================================================================

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog=os.path.basename(__file__),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=f"{APP_NAME} v{VERSION} - ARP entry validator, by {AUTHOR}",
        epilog=textwrap.dedent(f"""\
            examples
              %(prog)s learn                what can be wrong with an ARP entry
              %(prog)s check                consistency only; transmits nothing
              %(prog)s check --verbose
              %(prog)s verify               re-ask the network (asks first)
              %(prog)s verify --ip 192.168.1.1 --yes
              %(prog)s approve 192.168.1.1 --label "the router"
              %(prog)s watch --interval 60
              %(prog)s check --fail-on-critical
              %(prog)s serve                http://127.0.0.1:5000

            The consistency checks need no privileges and transmit nothing.
            Verification broadcasts ARP requests and needs root.

            {DISCLAIMER_LONG}
            """))
    p.add_argument("--db", default=DEFAULT_DB,
                   help=f"SQLite database file (default: {DEFAULT_DB})")
    p.add_argument("--version", action="version", version=f"{APP_NAME} {VERSION}")
    sub = p.add_subparsers(dest="cmd")

    def common(s):
        s.add_argument("--verbose", action="store_true")
        s.add_argument("--quiet", action="store_true", help="hide informational findings")
        s.add_argument("--show", type=int, help="limit how many findings are printed")
        s.add_argument("--fail-on-critical", action="store_true",
                       help="exit non-zero on any critical finding")
        s.add_argument("--fail-over", type=float,
                       help="exit non-zero if the score exceeds this")
        s.add_argument("--note")
        return s

    s = common(sub.add_parser("check", help="validate the cache; transmits nothing"))
    s.set_defaults(func=cmd_check)

    s = common(sub.add_parser("verify", help="re-ask the network whether entries are true"))
    s.add_argument("--ip", help="verify only this address")
    s.add_argument("--wait", type=float, default=0.6,
                   help="seconds to listen for replies per address")
    s.add_argument("--yes", action="store_true", help="skip the confirmation prompt")
    s.set_defaults(func=cmd_verify)

    s = sub.add_parser("watch", help="validate repeatedly, report only what is new")
    s.add_argument("--interval", type=float, default=60.0)
    s.add_argument("--count", type=int)
    s.add_argument("--quiet", action="store_true")
    s.set_defaults(func=cmd_watch)

    s = sub.add_parser("pairs", help="every address pairing seen")
    s.add_argument("--limit", type=int, default=60)
    s.set_defaults(func=cmd_pairs)

    s = sub.add_parser("approve", help="accept a pairing as expected")
    s.add_argument("target", help="an IP, a MAC, or the full key")
    s.add_argument("--label")
    s.add_argument("--note")
    s.set_defaults(func=cmd_approve)

    s = sub.add_parser("revoke", help="undo an approval")
    s.add_argument("target")
    s.set_defaults(func=cmd_revoke)

    s = sub.add_parser("learn", help="what can be wrong with an ARP entry")
    s.set_defaults(func=cmd_learn)

    s = sub.add_parser("scans", help="previous checks")
    s.add_argument("--limit", type=int, default=25)
    s.set_defaults(func=cmd_scans)

    s = sub.add_parser("serve", help="start the web app")
    s.add_argument("--host", default="127.0.0.1")
    s.add_argument("--port", type=int, default=5000)
    s.add_argument("--debug", action="store_true")
    s.set_defaults(func=cmd_serve)

    s = sub.add_parser("export", help="write a report to a file")
    s.add_argument("--scan", type=int)
    s.add_argument("--format", choices=["json", "csv", "html"], default="html")
    s.add_argument("--out")
    s.set_defaults(func=cmd_export)

    s = sub.add_parser("logs", help="local event log")
    s.add_argument("--level", choices=["INFO", "WARN", "ERROR", "info", "warn", "error"])
    s.add_argument("--limit", type=int, default=50)
    s.set_defaults(func=cmd_logs)

    s = sub.add_parser("purge", help="delete stored checks")
    s.add_argument("--keep", type=int, default=50)
    s.add_argument("--all", action="store_true")
    s.add_argument("--pairs", action="store_true",
                   help="with --all, also delete the pair list and approvals")
    s.set_defaults(func=cmd_purge)

    s = sub.add_parser("selftest", help="verify every component (temporary database)")
    s.set_defaults(func=cmd_selftest)

    s = sub.add_parser("version", help="versions, interfaces and the disclaimer")
    s.set_defaults(func=cmd_version)
    return p


def main(argv=None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    set_db_path(args.db)
    if not getattr(args, "cmd", None):
        parser.print_help()
        return 0
    if args.cmd != "selftest":
        init_db()
    try:
        rc = args.func(args)
        return rc if isinstance(rc, int) else 0
    except BrokenPipeError:
        try:
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        except Exception:
            pass
        return 0
    except KeyboardInterrupt:
        print("\nInterrupted.")
        return 130
    except sqlite3.OperationalError as e:
        print(f"Database error: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
