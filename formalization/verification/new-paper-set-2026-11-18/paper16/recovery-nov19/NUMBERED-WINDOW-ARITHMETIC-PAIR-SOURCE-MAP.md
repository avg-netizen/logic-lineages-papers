# Concrete natural pairing and partial inverse (support only)

Paper16 ordinals.tex lines 13–28 (one numerical typed universe), 69–84
(finite numerical certificates, least-code representatives permitted,
arithmetic transitions and disjoint operator tags). The source leaves
the actual Gödel coding convention open. This thin preparatory packet
chooses a concrete natural pairing, but it does not yet code Ty, Head,
NTerm/NArgs, contexts, finite trace certificates or ordinal objects.

- The polynomial is literally `(a+b)*(a+b)+a` on natural numbers.
  The identical prior arithmetic-pair convention in
  `GorbowRegistryTuple.lean` is provenance only. This new module
  imports only Lean core, makes no existing source edits and transfers
  no proof status from the prior paper or old numbered carrier.
- Decoder candidates are all actual ordered pairs in
  `List.range (n+1) × List.range (n+1)`. The bound on both components
  is a theorem to be proved, not a supplied or assumed search oracle.
  Runtime `find?` checks the exact polynomial equality. Targets pay
  injectivity, exact sound+complete successful partial decoding,
  genuine roundtrip at every encoded pair, and exact rejection of
  never-encoded numerals. No arbitrary bound hypothesis.
- This is external executable natural coding with kernel equality
  proofs only. It does not assert primitive-recursive program/formula
  compilation, internal PA/ID1 arithmetic, a least class representative,
  a coded finite-context universe, a numerical rule checker or
  arithmetic accessibility. Actual syntax/contexts, checked class
  enumeration and actual RS will need separate exact bridges.
