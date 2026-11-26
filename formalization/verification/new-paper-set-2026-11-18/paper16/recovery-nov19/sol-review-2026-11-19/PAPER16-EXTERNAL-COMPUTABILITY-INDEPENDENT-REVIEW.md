# Paper 16 typed computability and downward closure

The four frozen statements match the external type recursion in `ordinals.tex` 100–110 and downward closure in 113–121. Ground computability uses the manuscript’s external guarded scalar predicate on the canonical code of a genuine quotient class. Code uniqueness proves agreement with any supplied actual canonical code. The arrow clause quantifies every actual class in the domain type and uses the literal auxiliary application class in the same lexical context. [Manuscript](../../../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex#L100) · [Typed predicate](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalComputability.lean) · [Frozen targets](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalComputabilityTargets.lean)

The positive-descendant proof uses actual ground accessibility at the base. At an arrow, it holds the argument fixed, lifts the positive function path on original classes, and applies the codomain induction hypothesis. The direct-descendant proof uses one actual `ClassEdge` as a positive `RS.one` path. Both clauses preserve the original signature, window, context and result type. This packet establishes the external predicate and its downward closure. The neutral and atomic cases, computability-to-accessibility implication, lambda case and internal ID₁ derivation require their own proofs. [Downward proof](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalComputabilityProof.lean) · [Application review](PAPER16-EXTERNAL-APPLICATION-INDEPENDENT-REVIEW.md)

## Verified edition

The frozen target SHA-256 is `62bec7e9ce3262d3902af99f52633193a89dc77f60e1babfa3c5eddfb4eb3e3a`. The native receipt `1795132400307512597-11` passed all 207 modules under the original serialized core profile. I matched all 39 freeze entries, both author entries, all 70 recursive pins, all module source and object hashes and the archived native receipt and axiom log. All four named declarations use only standard axioms. [Freeze](../NUMBERED-WINDOW-EXTERNAL-COMPUTABILITY-FROZEN.json) · [Author manifest](../NUMBERED-WINDOW-EXTERNAL-COMPUTABILITY-AUTHOR-MANIFEST.json) · [Recursive evidence](../NUMBERED-WINDOW-EXTERNAL-COMPUTABILITY-LOCAL-EVIDENCE.json) · [Receipt](../numbered-window-external-computability-native/1795132400307512597-11/1795132400307512597-11.json) · [Named axiom log](../numbered-window-external-computability-native/1795132400307512597-11/1795132400307512597-11-LogicLineages-PersistentMarking-NumberedWindowExternalComputabilityChecks.log)

| File | SHA-256 |
| --- | --- |
| Freeze | `4e2694b0f5d63b6f1529ae9ef975614c0a4ae1c54005b4190a9af993c9c2070d` |
| Author manifest | `c86e736526a10f4034969cb588486517075fd5a373bf11d451f71d2408751ba9` |
| Recursive evidence | `b665dfcf19f679c4759d7939cdc1220fcf130ba6ab2ebd3b8d9bc6443e375b50` |
| Native receipt | `e8a9a3ce54e35ccf2560ee5c5c9116d2116424d10ed6543f6b522663d97005ff` |
