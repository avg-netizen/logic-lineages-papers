# Actual Computable closure of the original atom map

One exact supporting contract is now proved and independently accepted:
when a payload operation is jointly Computable in its runtime parameters and
payload code, the unchanged radix-six `LinearRows.Code.mapAtoms` is jointly
Computable in those same parameters and the actual formula code.

The proof covers every numeric code. It retains the original parser,
constructor tags and payload behavior. It constructs the actual Computable
recursion using explicit children, assembly and code measure, with proved
strict descent and the literal recursion equation. The target adds no
DecidableEq or Inhabited premise on the parameter type and makes no Primrec
claim. The existing primitive-recursive supplier was not used to strengthen a
merely Computable payload.

Eight new Lean modules contain the frozen target and preflight, helper
semantics, four small proof modules and direct exact alias gate. All ten proof
declarations and the one alias have named native axiom audits using only
`propext`, `Classical.choice` and `Quot.sound`. No imported namespace was
enumerated. The complete gate has 553 source- and object-matched successful
local native rows. All inherited mathematical sources and control pins are
unchanged.

Current immutable receipts:

- `1794305904793518090-46.json`: target-only preflight passed.
- `1794307662610362332-45.json`: all focused proof modules and ten named audits passed.
- `1794307943791404168-45.json`: the direct frozen target alias and its named audit passed.

Exact source paths, SHA256 hashes, receipt hashes and the independent acceptance
hash are in `SOURCE-HASHES.json`. Raw evidence is not included in this small
checkpoint. Every successful checker was waited/reaped, its session exited
zero, and both shared locks were free at final closeout.

The original serialized limits were retained: 2,048 MiB heap, 1,536 MiB RSS,
2,048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall seconds
per compiler. No cold upstream build occurred.

This is a generic supporting closure lemma. Its payload-computability premise
must be discharged by actual checked programs in concrete consumers.
Block-atom/formula calibration, numeric elimination assembly and original BASE
remain pending. No numbered statement, full-root build or remote-CI pass is
claimed; root imports, register, manuscripts, CI and toolchain remain unchanged.
