#!/usr/bin/env python3
"""Heuristic scan: private declarations referenced from the public interface of a twin.

Under `@[expose] public section`, the public interface of a file consists of every
non-private declaration's header (type) and the bodies of non-private def/abbrev/
instance declarations.  A private name referenced there is rejected by the module
system ("would need to be public to access here").  Reports, per legacy module in
the closure of the roots, the private names so referenced and where.

Usage: private_scan.py ROOT_MODULE [...] [--json OUT]
"""
import json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
import import_graph as ig  # noqa: E402

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(private|protected)\s+)?(?:noncomputable\s+)?(?:partial\s+)?"
                  r"(def|abbrev|theorem|lemma|instance|structure|inductive|class)\b\s*([^\s:({\[]*)", re.M)


def decls(text):
    code = ig.strip(text)
    starts = [m for m in DECL.finditer(code)]
    out = []
    for k, m in enumerate(starts):
        end = starts[k + 1].start() if k + 1 < len(starts) else len(code)
        chunk = code[m.start():end]
        out.append((m.group(1) == "private", m.group(2), m.group(3), chunk, code.count("\n", 0, m.start()) + 1))
    return out


def main(argv):
    out_json = None
    if "--json" in argv:
        i = argv.index("--json"); out_json = argv[i + 1]; argv = argv[:i] + argv[i + 2:]
    report = {}
    for m in ig.closure(argv):
        p = ig.src(m)
        if p is None or not m.startswith("LogicLineages."):
            continue
        text = p.read_text()
        if ig.strip(text).lstrip().startswith("module"):
            continue
        ds = decls(text)
        priv = {name.split(".")[-1]: kind for is_p, kind, name, _, _ in ds if is_p and name}
        if not priv:
            continue
        hits = []
        for is_p, kind, name, chunk, line in ds:
            if is_p:
                continue
            if kind in ("def", "abbrev", "instance", "structure", "inductive", "class"):
                exposed = chunk
            else:
                exposed = chunk.split(":=", 1)[0]
                if " by" in exposed.split(":", 1)[-1][:0]:
                    pass
            for pn in priv:
                if re.search(r"(?<![\w.'])" + re.escape(pn) + r"(?![\w'])", exposed):
                    hits.append({"private": pn, "private_kind": priv[pn], "user": name, "user_kind": kind,
                                 "line": line})
        if hits:
            report[m] = hits
    names = sorted({(m, h["private"]) for m, hs in report.items() for h in hs})
    print("files", len(report), "distinct private names", len(names))
    for m, hs in report.items():
        print(m.split(".")[-1], sorted({(h["private"], h["private_kind"]) for h in hs}))
    if out_json:
        Path(out_json).write_text(json.dumps(report, indent=1) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:])
