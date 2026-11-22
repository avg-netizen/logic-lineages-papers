# Paper 17: exact primitive-recursive signed grouping code

Printed anchor: `arithmetic.tex`, `thm:arithmetic`, arithmetic signed
grouping before high-stratum greatest-class reduction. This packet pays
only the raw grouping effectivity of the canonical first-occurrence tape.

- Structured input is the genuine existing `List (Int × LowerOperandCode)`
  and serialized input uses its actual `Encodable` instance, not newly
  allocated syntax tags or unsigned coefficient truncation. The
  primitive-recursive reverse/dedup/reverse stage tests exact raw key
  equality; the dedup fold is calibrated to the same checked list
  operation. The list fold sums exact signed Int weights and removes
  exactly zeros.
- `groupCheckedRaw` and `groupCode` retain the separate explicit
  all-original-occurrences-read-success input. No executable reader or
  proof that an arbitrary caller's Boolean reports actual hits is given.
  A byte list that fails to deserialize returns none, not a successful
  empty list. This scope makes no semantic validity claim for successfully
  decoded keys outside the original typed encode image.
- On a truly encoded typed tape with the explicit gate, the output is
  byte-for-byte the checked canonical typed grouping, by the already
  verified #1319 calibration. No equality with legacy Finsupp enumeration,
  tie-dependent output, or whole zero-transition compiler.

Three exact named aliases at
`LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodeStatementChecks`.
Author-side source-only; tests by the coordinator.
