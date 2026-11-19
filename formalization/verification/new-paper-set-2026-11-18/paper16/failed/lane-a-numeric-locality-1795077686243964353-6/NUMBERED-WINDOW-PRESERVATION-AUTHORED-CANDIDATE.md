# Numeric window preservation: authored candidate, not checked

Exact root: `LogicLineages.PersistentMarking.NumberedWindowPreservationChecks`.
Frozen comparator and source map are unchanged. Target-only original-core
preflight NUMERIC-LOCALITY-TARGET-0824 passed all 22 rows, max 495804 KiB,
receipt `1795076623319733979-6`; reaped and both shared locks clear.
Current proofs are unbuilt and independently unaccepted.

| New proof module (prefix NumberedWindowPreservation) | Actual derivation |
| --- | --- |
| GuardProof | Project and assemble typed node, binder, and original declaration guards; actual object type checked by the established typed annotation theorem. No change to the carrier. |
| BoundProof | Numeric de Bruijn shift fusion; pushed-binder substitution equality. Variable-image guard only for encountered bound annotations already in K, not every irrelevant annotation in an outside context. Discharge one removed binder from its actual admitted argument, and preserve each other bound lookup. |
| SubstitutionProof | Mutual typed syntax recursion over terms and ordered base/extras, using the concrete variable-image proof. `beta` instantiates the same actual substitution as the frozen raw rule at depth zero. |
| ReplacementProof | Explain exact source and target membership via the literal `List.Perm` certificates. Every inserted concrete occurrence originates in a removed one by `MarkDecrease`, along common lambda prefix, preserving types and declarations. |
| HeadProof | Recover Select's actual base or extra occurrence with its typed annotation; descend its actual arrow prefix; retype entire unchanged original owner copies; realize the actual left-associated auxiliary call. Copy uses the guard of the actual target head and its declaration's argument types. |
| RawProof | Mutual recursion on existing raw term/argument witnesses. Internally track annotated result type and literal support/heads from the typed source; do **not** claim skeletal Stat preserves lexical typing. Externally combine the resulting footprint with the independent typed target premise of the frozen exact comparator. There is only auxiliary function-side closure. |
| PrimaryCases / PrimaryProof | Induct over the actual fixed-window primary equivalence and ordered typed argument congruence witnesses; transport complete guards in both directions. Root exchanges use the target/source original window guards and true permutation of typed base occurrences. Congruence leaves fixed label/current result and order of extras; no raw argument-side closure. |
| Checks | Three exact frozen aliases, with printed axiom audit. Actual typed trace induction pays every source and final vertex from initial admission: raw steps use independently stored lexical successor typing, and equivalence uses the proved guard transfer. |

No frozen source/target or existing module edited. No proof/caps borrowed
from historical status and no skeleton/window target-by-definition.
Supports numeric preservation only; not yet the construction of all
required positive simulations or full numbered locality. Nothing in
this packet proves the ID1 accessibility theorem.

## Current proof-only hashes

```text
5a5fd94efb0b9864ebf54d0bcb29a9ddc7006b6754648eebadc770a1412a4939  LogicLineages/PersistentMarking/NumberedWindowPreservationGuardProof.lean
8e744b197be4906ba30b151c3ec14bbc64d694718971a5d6bc2bab870c1baf66  LogicLineages/PersistentMarking/NumberedWindowPreservationBoundProof.lean
07c5b684d7eed3f84950f1624c29031b2da43939ee28b08efb3422a0a2ba0540  LogicLineages/PersistentMarking/NumberedWindowPreservationSubstitutionProof.lean
285c3cba4a77e14809c08702a33ca928c7323cedc6e545db217c7c1101d59c62  LogicLineages/PersistentMarking/NumberedWindowPreservationReplacementProof.lean
4cc2838ee4531a803129ceab7bb77cbfc7ec286e3f54de7716d61110d34a5721  LogicLineages/PersistentMarking/NumberedWindowPreservationHeadProof.lean
7e8911863e5b0ebcbc8579ceb286064641f4ea5b22d2ec699dc1a3b5a9dcddcb  LogicLineages/PersistentMarking/NumberedWindowPreservationRawProof.lean
30a21b2404a71caa54ccde75525c5d2fd4a25ca0bdb9bf6638b6a7ad9ff2fbb3  LogicLineages/PersistentMarking/NumberedWindowPreservationPrimaryCases.lean
969194801ba1e13d6f331d3df891ba8ba0768fe2c61c811441054aa04ddfa987  LogicLineages/PersistentMarking/NumberedWindowPreservationPrimaryProof.lean
1e64c950506e125ad422f2d3db465cee6c744fcbf759430c341cfe5239194c3e  LogicLineages/PersistentMarking/NumberedWindowPreservationChecks.lean
```
