# Paper 16 external application and scalar accessibility

The four frozen statements match the external application and accessibility argument in `ordinals.tex` 123–127. The final native and recursive evidence matches the current source. [Manuscript](../../../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex#L123) · [Frozen targets](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalApplicationTargets.lean)

| Exact alias | Independent source correspondence |
| --- | --- |
| `exact_QuotientApplicationLiteral` | `appCarrier` constructs the literal `.auxApp` at the actual σ and τ. Its operands inhabit the same original signature, window and lexical context. The manuscript assumes a finite subtype-closed window, and the existing admission proof preserves the entire original head inventory. `appClass` is well-defined by the two actual `Primary` congruences. |
| `exact_QuotientAppPreservesPositive` | Each `ClassEdge` witness supplies actual admitted representatives and a raw step. The proof places that step in the function position with the same representative of the fixed argument. Induction preserves each `RS.one` and `RS.more` constructor, so the result still contains a genuine raw step. |
| `exact_ScalarClassAccessibility` | The address decoder identifies the same finite context, result type and least code at the source end of each `AddressPositive` witness. Actual canonical-code fibers identify its source class. In the other direction, the code of each descendant comes from actual class-code totality. Both induction directions carry the original guarded predicate and original quotient relation. |
| `exact_ExternalIApplicationPullback` | The proof translates external `I(QU)` to accessibility of `appClass Q U`. Each actual positive descendant `Q′` maps to a positive descendant `Q′U` with that same `U`. Induction on accessibility of `QU` proves accessibility of `Q`; the source code equivalence gives external `I(Q)`. The pullback uses only preservation of positive paths. |

[Literal application](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalApplication.lean) · [Positive lift](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalApplicationPathProof.lean) · [Scalar code correspondence](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalScalarClassProof.lean) · [Pullback](../../../../../LogicLineages/PersistentMarking/NumberedWindowExternalApplicationPullbackProof.lean)

The implication applies to any admitted argument at type σ. The next step in the manuscript obtains the premise from the typed computability clause and a computable fresh variable. That step and the internal ID₁ argument remain separate obligations.

## Verified edition

The target-only preflight `1795132257369592299-10` matched `NumberedWindowExternalApplicationTargets.lean` SHA-256 `581f1c623e766fbdeac36b2279ee4f5a2630de430a738e7e14624ccda7354c8a`. I independently matched all 36 freeze entries and four author entries, the 69 recursive pins, all 203 module sources and objects and the archived passing receipt and named axiom log. All four aliases use axioms from `propext`, `Classical.choice` and `Quot.sound` only. The receipt passed under the original serialized core profile. [Freeze](../NUMBERED-WINDOW-EXTERNAL-APPLICATION-FROZEN.json) · [Author manifest](../NUMBERED-WINDOW-EXTERNAL-APPLICATION-AUTHOR-MANIFEST.json) · [Recursive evidence](../NUMBERED-WINDOW-EXTERNAL-APPLICATION-LOCAL-EVIDENCE.json) · [Native receipt](../numbered-window-external-application-native/1795132303289043673-10/1795132303289043673-10.json) · [Named axiom log](../numbered-window-external-application-native/1795132303289043673-10/1795132303289043673-10-LogicLineages-PersistentMarking-NumberedWindowExternalApplicationChecks.log)

| File | SHA-256 |
| --- | --- |
| Manuscript `ordinals.tex` | `526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5` |
| Freeze | `b5b46d12fcb77bd068fb589969cdbb33e0fe0a9c71add88a0859159b4ea27a57` |
| Author manifest | `5ff3ea319c4c4407d74485f8dd2dbf823ed43b72924b9e550216c876e4e0aeb6` |
| Recursive evidence | `fc47898ffda9d38e01131b0c1c650a41c83e00fd319277e80f9485256e89440b` |
| Passing receipt `1795132303289043673-10` | `38037ec2302bdbde749b5b78865d7d19384aed529ceb05613b57ba1e70e4c1e6` |
| Exact alias module | `59bc95609a7477b72d718aa7962fb8c5fb7724b6d9c054b9bd0e7c190b9922a7` |
