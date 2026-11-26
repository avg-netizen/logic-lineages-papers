#!/usr/bin/env python3
"""Summarize a scripts/check.py build receipt: per-status counts, peak RSS, seconds.

Usage: receipt_stats.py build-reports/<id>.json [--top N]
"""
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
p = Path(sys.argv[1])
if not p.is_absolute():
    p = ROOT / p
d = json.load(open(p))
mods = d.get("modules", [])
top = int(sys.argv[sys.argv.index("--top") + 1]) if "--top" in sys.argv else 5
status = {}
for m in mods:
    status[m.get("status")] = status.get(m.get("status"), 0) + 1
rss = [(m.get("peak_process_tree_rss_kib") or 0, m["module"]) for m in mods]
secs = [(m.get("seconds") or 0, m["module"]) for m in mods]
cpu = [(m.get("observed_cpu_seconds") or 0, m["module"]) for m in mods]
twin = [m for m in mods if ".NativeModule." in m["module"]]
print("receipt", p.name, "modules", len(mods), "twins", len(twin), "status", status,
      "rss_cap_mib", d.get("rss_cap_mib"), "returncode/overall", d.get("returncode", d.get("status")))
print("peak RSS kib max", max(rss)[0] if rss else None, "at", max(rss)[1] if rss else None)
print("sum seconds all", round(sum(s for s, _ in secs), 2), "twins", round(sum(m.get("seconds") or 0 for m in twin), 2))
print("sum cpu all", round(sum(s for s, _ in cpu), 2))
for r, m in sorted(rss, reverse=True)[:top]:
    print("  rss", r, m)
for s, m in sorted(secs, reverse=True)[:top]:
    print("  sec", s, m)
bad = [m for m in mods if m.get("returncode") not in (0, None)]
for m in bad:
    print("FAILED", m["module"], m.get("returncode"), m.get("log"))
