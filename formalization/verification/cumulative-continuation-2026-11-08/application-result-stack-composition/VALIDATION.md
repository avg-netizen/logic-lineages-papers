# Validation of exact output-preserving composition

The four frozen target types and all prior source pins are unchanged.
Independent static review accepted the specification before the three
specification modules passed native preflight. Proof authorship began only
after both steps. No target, quantifier, premise, conclusion or AST amendment
was needed.

## Checked results

- Terminal iteration preserves the actual empty-work live state at every
  symbolic count and every arbitrary result stack.
- Run zero is equivalent to empty initial work and equality of whole result
  codes, using the actual state constructors and numeric iterator graph.
- Work append preserves the exact final results at the summed counts. The
  internal induction handles prefix completion before the stated count by
  stabilizing the final state and padding the suffix execution.
- Result suffix framing preserves work and count while appending the same
  arbitrary background to the initial and final results. The internal
  induction separates actual failure from live successors and excludes
  failure using the original successful run.

One-step simulation covers visits, opened and rejected root guards, finish
frames, malformed frame tags, and both empty/singleton-result underflows.
The proof-only optional extension helper is exactly original append when
enabled and an input projection otherwise. No semantic simulation relation
or external truth-to-derivability assumption is introduced.

The exact gate checks four aliases against the original preflight
comparators and prints each actual axiom closure. Every closure uses only
`propext`, `Classical.choice` and `Quot.sound`. There are 83 supporting
namespace theorem audits in addition to the four exact aliases.

## Evidence and limits

`SOURCE-PINS.json` records the 1,148-module local import closure, including
meta imports. Every current source matches a successful immutable native
receipt. This reuses earlier matching receipts; it does not claim a fresh
whole-closure build. The 19 component files are included in the explicit
portable allowlist in `ACCEPTANCE.json`. The reviewed specification,
correspondence, manuscript and selected prerequisite pins all match.

All checks used one serialized compiler through `scripts/check.py`, with
2,048 MiB heap, 1,536 MiB RSS, 2,048 MiB minimum free memory, one thread,
90 CPU seconds and 180 wall seconds. No upstream cache rebuild or resource
increase occurred. Peak successful component RSS was 1,151,492 KiB.
Failed candidates and all native receipts/logs are retained locally.

The exact gate and all owned checker sessions completed. Both serialized
locks were verified free and released to the coordinator. No Git operation,
remote CI, full-root build, numbered source promotion or downstream fold/
representative theorem is claimed.
