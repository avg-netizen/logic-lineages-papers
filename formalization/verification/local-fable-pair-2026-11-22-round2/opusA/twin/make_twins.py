#!/usr/bin/env python3
"""Generate module-system twins of legacy LogicLineages modules (copied from Opus B's opusB/twin/make_twins.py;
adapted by Opus A for the realization closure: own manifest, and SKIPS every twin file that already exists
unless this manifest already records it, so Opus B's twins are never regenerated or overwritten).

Usage: make_twins.py ROOT_MODULE [ROOT_MODULE ...]

For every *legacy* local module in the import closure of the roots, writes
LogicLineages/NativeModule/<rest of path>.lean with
    module
    <header comments of the original, if any>
    public import <twin or unchanged module>   (one per original import)
    @[expose] public section
    <blank line>
    <ORIGINAL BODY BYTES>
Module-system originals in the closure are imported unchanged (a module file never
imports a legacy one, so no twin is needed below them).  External imports (Init, Std,
Lean, Mathlib) are kept with `public import`.

"Body" = the original file text from the first character that is not part of the
leading import block (blank lines, comments and `import` lines) to the end of file.
The twin's body is the text after the inserted `@[expose] public section\n\n` line.
`body_unchanged` compares the two byte-for-byte.

Body edits are only those listed in BODY_EDITS (exact old -> new, with a reason); each
applied edit is recorded in the manifest with a unified diff.

Never writes outside LogicLineages/NativeModule/ and this lane's twin/ directory, and
never overwrites an existing twin whose content would change unless --refresh is given.
"""
import difflib, hashlib, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]          # .../formalization
sys.path.insert(0, str(HERE.parents[1]))
import import_graph as ig       # noqa: E402  (read-only helper in the round directory)

PREFIX = "LogicLineages."
TWIN_PREFIX = "LogicLineages.NativeModule."
MANIFEST = HERE / "TWIN-MANIFEST-REALIZATION.json"

# file module name -> list of (old, new, reason).  Filled only when a gate shows need.
# Reason for every entry below: under `@[expose] public section` the module system rejects a
# private declaration referenced from the public interface (a public theorem's statement or an
# exposed public def body): "A private declaration `X` (from the current module) exists but would
# need to be public to access here" (gate 1795399074444699902-3255016 on the first of them).
# The minimal change deletes the single word `private` on that declaration; the name, namespace,
# statement and body are unchanged.  Sites found by twin/private_scan.py.
_PRIV = ("private def", "def",
         "module system: private declaration referenced from the public interface of this file; "
         "delete the word `private` (one word)")
BODY_EDITS: dict[str, list[tuple[str, str, str]]] = {
    "LogicLineages.PersistentMarking." + f: [(_PRIV[0] + " " + n + " ", _PRIV[1] + " " + n + " ", _PRIV[2])
                                            for n in names]
    for f, names in {
        "NumberedWindowExternalApplication": ["applyRepresentative"],
        "NumberedWindowPrimarySequenceTermLift": ["termMap"],
        "NumberedWindowPrimarySequenceBaseLift": ["fromArgs"],
        "NumberedWindowExternalWindowSubstitutionRawProof": ["TermClaim"],
        "NumberedWindowPreservationRawProof": ["TermClaim"],
        "NumberedWindowRealizationWindowProof": ["DeclaredTerm"],
        "NumberedWindowSourceInventoryProof": ["TermAdmitted"],
        "NumberedWindowTraceTypingProof": ["PairListType", "PairType"],
    }.items()
}


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def is_module_system(text: str) -> bool:
    return ig.strip(text).lstrip().startswith("module")


def split_header(text: str):
    """Return (header_text, body_text) where header is the leading import block."""
    i, n = 0, len(text)
    last_end = 0
    while i < n:
        if text.startswith("/-", i) and not text.startswith("/-!", i) and not text.startswith("/--", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j): depth += 1; j += 2
                elif text.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            i = j; last_end = i; continue
        if text.startswith("--", i):
            j = text.find("\n", i); j = n if j < 0 else j + 1
            i = j; last_end = i; continue
        if text[i] in " \t\r\n":
            i += 1; continue
        m = re.compile(r"import[ \t]+[^\n]*\n?").match(text, i)
        if m:
            i = m.end(); last_end = i; continue
        break
    # body starts at the first significant char after the import block; keep the
    # whitespace between the last header item and the body inside the header.
    body_start = i
    return text[:body_start], text[body_start:]


def twin_name(m: str) -> str:
    assert m.startswith(PREFIX)
    return TWIN_PREFIX + m[len(PREFIX):]


def twin_path(m: str) -> Path:
    return ROOT / (twin_name(m).replace(".", "/") + ".lean")


def orig_path(m: str) -> Path:
    return ROOT / (m.replace(".", "/") + ".lean")


def main(argv):
    refresh = "--refresh" in argv
    roots = [a for a in argv if not a.startswith("--")]
    order = ig.closure(roots)
    legacy = set()
    for m in order:
        p = ig.src(m)
        if p is None or not m.startswith(PREFIX):
            continue
        if not is_module_system(p.read_text()):
            legacy.add(m)
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {"twins": {}}
    written = kept = 0
    skipped = []
    for m in order:
        if m not in legacy:
            continue
        op = orig_path(m)
        raw = op.read_bytes()
        text = raw.decode()
        header, body = split_header(text)
        imports = []
        for line in ig.IMPORT.findall(ig.strip(header)):
            for d in line.split():
                imports.append(twin_name(d) if d in legacy or (ig.src(d) is not None and d.startswith(PREFIX)
                               and not is_module_system(ig.src(d).read_text())) else d)
        comments = "".join(l + "\n" for l in header.splitlines()
                           if l.strip() and not re.match(r"\s*import\s", l))
        new_body = body
        edits = []
        for old, new, reason in BODY_EDITS.get(m, []):
            assert new_body.count(old) == 1, (m, old)
            before = new_body
            new_body = new_body.replace(old, new)
            diff = "".join(difflib.unified_diff(before.splitlines(True), new_body.splitlines(True),
                                                str(op.relative_to(ROOT)), "twin body", n=0))
            edits.append({"old": old, "new": new, "reason": reason, "diff": diff})
        twin = ("module\n\n" + comments + "".join(f"public import {d}\n" for d in imports)
                + "\n@[expose] public section\n\n" + new_body)
        tp = twin_path(m)
        tb = twin.encode()
        if tp.exists() and m not in manifest["twins"]:
            skipped.append(m)
            continue
        if tp.exists() and tp.read_bytes() != tb and not refresh:
            raise SystemExit(f"twin exists with different content: {tp} (use --refresh)")
        if not tp.exists() or tp.read_bytes() != tb:
            tp.parent.mkdir(parents=True, exist_ok=True)
            tp.write_bytes(tb); written += 1
        else:
            kept += 1
        twin_body = twin.split("\n@[expose] public section\n\n", 1)[1]
        manifest["twins"][m] = {
            "original_path": str(op.relative_to(ROOT)),
            "original_sha256": sha(raw),
            "original_body_sha256": sha(body.encode()),
            "twin_module": twin_name(m),
            "twin_path": str(tp.relative_to(ROOT)),
            "twin_sha256": sha(tb),
            "twin_body_sha256": sha(twin_body.encode()),
            "body_unchanged": twin_body == body,
            "body_edits": edits,
        }
    manifest["generator"] = str(Path(__file__).relative_to(ROOT))
    manifest["generator_sha256"] = sha(Path(__file__).read_bytes())
    manifest["body_definition"] = ("original text after the leading block of blank lines, non-doc comments and "
                                   "`import` lines; twin text after the inserted `@[expose] public section` line "
                                   "and one blank line")
    manifest["header_rule"] = ("`module`, original non-import header comments, `public import` of each original "
                               "import (legacy local -> LogicLineages.NativeModule twin; module-system or "
                               "external unchanged), blank line, `@[expose] public section`, blank line")
    manifest["skipped_existing"] = sorted(set(manifest.get("skipped_existing", [])) | set(skipped))
    manifest["skip_rule"] = ("a twin file that already exists and is not recorded in this manifest belongs to another "
                             "lane (Opus B) and is neither regenerated nor overwritten; it is listed in skipped_existing")
    manifest["count"] = len(manifest["twins"])
    manifest["body_changed"] = sorted(k for k, v in manifest["twins"].items() if not v["body_unchanged"])
    MANIFEST.write_text(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
    print(f"closure {len(order)} legacy {len(legacy)} written {written} unchanged {kept} "
          f"manifest {manifest['count']} body_changed {len(manifest['body_changed'])} skipped_existing {len(skipped)}")
    print("root twins:", " ".join(twin_name(r) for r in roots if r in legacy))


if __name__ == "__main__":
    main(sys.argv[1:])
