# Original fresh probe: arbitrary-open object output split

Source: Paper16 `sections/ordinals.tex`, lines112–127. In the external
type induction, applying the original typed source to a fresh **computable**
variable is needed before the fixed-argument accessibility pullback. This
packet pays a strictly supporting arithmetic/logic part: the original fresh
selector's option output has a genuine object case split on arbitrary open
terms. The rejecting case is **not** ruled out by this packet.

| Frozen comparator | Actual object judgment and original source correspondence |
| --- | --- |
| `rejectedAt` | Original unary Program graph `programGraph a zero ![q]`, the numeral zero encoding `none`. No new graph or verifier. |
| `chosenAt` | Original `freshAt a q u` from checked #611 uses output `succ u`; existential binds exactly that (u), with (q) relabelled over the new variable. No independent choice/name. |
| `FreshProbeOutputCases` | Original graph output split `rejectedAt ⊔ chosenAt` is an actual derivation in every open type/context and for every ordinary arithmetic input term, stronger than the empty-context instance. Any fixed positive body is allowed, hence the same numbered `sourceBody d c` is an instance. |
| `FreshProbeRejectedExcludes` | Original zero output entails the negation of a newly asserted successor output for the identical program/input, for every (u). |
| `FreshProbeUnique` | Two asserted successor outputs at the identical program/input imply equality of their payloads (not source equivalence or arbitrary convertibility). |
| `ExactOriginalFreshProbeObjectCases` | Specializes the generic split to the actually selected unary `a` whose value is the code of `NumberedWindowTypedProbe.probe s n` on **every** raw (n). The program supplying the calibration is the very same one in the graph. Uniqueness/exclusivity for any previously selected calibrated (a) follow from the universal contracts. |

Intended proof path (not yet authored): `InternalRecursionClosureProof.actualOriginalPrograms`
gives output existence and functionhood of the **actual original compiler** on all
term instances. Existentially choose the original output and use object PA
zero-or-successor from `InternalLinearCombinationZeroRemainderProof`; transport
the identical output graph along the two indicated equalities using the
syntactic instantiated graph formula. Exclude zero/successor jointly by
functionhood and the PA successor axiom; compare two successor payloads by
object successor injectivity. No standard-natural realization is inverted and
no numerical truth is turned into an object derivation. The accepted
`exact_TypedProbePrograms` existential pays the actual option-code calibration.

Not claimed: `TypedProbeTotal` (typed guard excludes rejection and supplies the
actual selected application, then yields the same codomain typed guard);
`FreshVariablesComputable` (requires the neutral/source rules, not successful
option encoding); the numbered arithmetic-accessibility lemma or any BH bound.
Closed-numeral checks #606/#614 and external numerical existence #613 do not
supply those arbitrary-open object judgments.
