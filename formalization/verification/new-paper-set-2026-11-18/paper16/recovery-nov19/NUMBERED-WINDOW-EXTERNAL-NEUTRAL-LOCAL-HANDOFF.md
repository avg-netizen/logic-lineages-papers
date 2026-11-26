# Paper 16 neutral application reducts

The proof supplies the direct reduction cases in `ordinals.tex` lines 113–121. The source's raw auxiliary application has beta, bottom and function-side rules. `Primary` may change either application slot through equivalence. The original positive class relation uses actual raw edge witnesses between arbitrary representatives. [Original manuscript](../../../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)

| Exact contract | Checked scope |
| --- | --- |
| `PrimaryPreservesNonLambda` | The original `Primary` relation preserves whether a term has a lambda at its root. |
| `ExactNonLambdaRepresentatives` | Non-lambda shape of a chosen representative is equivalent to non-lambda shape of every representative of the same actual class. |
| `PrimaryAuxApplicationComponents` | An equivalent representative of a literal auxiliary application retains its application constructor and both literal types. Its two entries are independently related by the original typed `Primary`. |
| `NonLambdaApplicationClass` | The actual quotient application always has non-lambda shape. |
| `NeutralApplicationEdges` | An actual direct reduct of an application with a non-lambda function is either the typed bottom class or the application of an actual one-edge function descendant to the same argument class. |

The last proof recovers the function and argument from the source representative of the supplied raw edge. It uses their original window admission and class equalities before eliminating the beta case. Function reduction retains the raw argument, and its class equality restores the original argument class in the target. Both endpoint windows stay fixed. The joint type induction and the internal ID₁ derivation remain separate proof obligations.

The target preflight passed in `1795132376477902773-9`. The exact gate passed in `1795132488080057490-9` under the original single-threaded core limits. Three new proof/check modules compiled and 39 modules were source- and object-matched cache hits. Peak RSS of the new modules was 474,112 KiB. The recursive verifier matched all 42 modules, 47 source pins and five exact aliases. The aliases use only `propext` and, for the last two, `Quot.sound`. [Target preflight](external-neutral-local-native/1795132376477902773-9.json) · [Exact native receipt](external-neutral-local-native/1795132488080057490-9.json) · [Axiom log](external-neutral-local-native/1795132488080057490-9-LogicLineages-PersistentMarking-NumberedWindowExternalNeutralChecks.log) · [Recursive evidence](NUMBERED-WINDOW-EXTERNAL-NEUTRAL-LOCAL-EVIDENCE.json)
