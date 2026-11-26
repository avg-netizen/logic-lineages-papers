# Paper 16: literal ascending numeral axis and named-leaf occurrence

Source only; exact native and named axiom checks pending. No stage grammar
program or frozen prior target is changed.

- The narrow `ascendingRange` singleton, append-right step and full
  original recursion are exactly the three ASTs in
  `Continuation20261117/MinimalOriginalPrimaryTypedCarrier/AST/OriginalAscendingRange/Definitions.lean`
  under the same underlying declarations. Its output uses the standard
  ordered scratch codec, including a literal zero index (not a miss).
  No original primary theory is imported.
- `exact_OpenCoverAscendingRangeMember` is forward only. From an actual
  output report and genuine object order `i < bound`, uses actual Nat
  induction on the bound. A successor recovers its original append row
  and actual singleton; the old index is carried by actual append left,
  the exact last index by actual cons head and append right, using
  supporting #892. An actual memo, external decoded list, backward
  interpretation, or a range inclusion premise is not required.
- `exact_OpenCoverNamedLeafAtLargerBound` uses actual open grammar type
  membership and the genuine formulas `i < suc m` and `m < suc M` to
  show `i < suc M`, retrieves that larger physical ascending range,
  and applies actual finite Cartesian-fold membership at the two
  literal axes of the named branch. The same `ty,i` yield the sparse
  `rawCons tag (rawCons ty (rawCons i 0))`, with tag 0/1 only;
  the containing list uses standard scratch cons. It needs the
  actual named output report, not a smaller leaf list, unproved
  cross-bound leaf premise, or arbitrary full grammar transport.
- The corresponding numerical calibration types are defined for later
  narrow proof, but this open packet does not claim or import that
  calibration. Backward provenance, nonnamed layers, cells, and
  full stage transport remain separate.

| Module | SHA-256 |
| --- | --- |
| `NumberedWindowInternalCoverAscendingRangeOpenDataProof` | `36663c51d1ef1a959e2f51ca5c5e40fab4d421749483745eff184ee7889dde73` |
| `NumberedWindowInternalCoverAscendingRangeOpenProof` | `d0914efe90d1734a33343169a90bc8f1abd8a5de4e477100da7079c631c1fba4` |
| `NumberedWindowInternalCoverAscendingRangeSyntaxProof` | `26d2669aca05511ac2d4d6d43a5edb857ac4f507caaed1733224b21dab901445` |
| `NumberedWindowInternalCoverAscendingRangeTargets` | `e20cbf0f3c053227232fc63b4a9862739302af1e9855a3722035ca790fd0b923` |
| `NumberedWindowInternalCoverNamedLeavesOpenDataProof` | `49ea80174e327f2e606232709ad7a5401c7b43729739d03688f4a38f510c6a6b` |
| `NumberedWindowInternalCoverNamedLeavesOpenProof` | `d4d866ff4885b3c35754102c32f0db14b785ceb35756517fb669ae7867918659` |
| `NumberedWindowInternalCoverNamedLeavesTargets` | `9c9e518d8e42cd435b5a4976f415fc07d983aa9a35d4fef4a33639829e7dc8e7` |
