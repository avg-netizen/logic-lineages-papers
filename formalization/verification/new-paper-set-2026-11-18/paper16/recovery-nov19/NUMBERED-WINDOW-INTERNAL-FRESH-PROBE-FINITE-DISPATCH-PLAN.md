# Original typed fresh-variable application: finite closed-window dispatch

Source: Paper16 `sections/ordinals.tex` 79–127. Work only with the already
selected fixed original signature S and finite subtype-closed original K,
over **all** actual context stack codes and all raw input numerals. This
packet would discharge the arithmetic/object `TypedProbeTotal d p h a c`
premise of checked #611, not the source `FreshVariablesComputable` premise.
No manuscript or previous frozen source changes.

## Program selection

Use the original `Program` AST type and `programGraph` compiler. The chosen
raw application guard `p : Program 3` stays exactly the #596 guard, or any
previously chosen p with the same supplied original calibration. The chosen
`a : Program 1` stays exactly the #608 original option-code selector,
calibrated on all raw numerals n to encode(probe s n). Use the existing
`ApplicationPrograms` first projection to choose `A : Program 2`, the
actual encode(application s q u), **not** a search or arbitrary midpoint.
Use the #608 ordinary typed recognizer `h0 : Program 2` only as a leaf.
All four original selected programs are retained literally, and none is
identified by extensional equality of Program ASTs.

For each external `Source.Ty` produce a unary verifier H:

* H at ground is h0 applied to [literal ground type code, q].
* H at σ→τ is original exact-one conjunction of h0([literal arrow code,
  q]) and a nested original conditional. Its outer control is the **same
  literal** a(q), with 0 returning zero. In its other branch compute
  u=pred(a(q)), preserving q; the inner control is A(q,u), with 0
  returning zero. In its other branch compute v=pred(A(q,u)), preserving
  q,u, and check exact-one conjunction p(q,u,v) and Hτ(v). Thus the
  complete AST uses only structural recursion on Lean's external Ty when
  selecting its finite branches, not new arithmetic induction or a
  second object-language inductive predicate.
* The chosen `h : Program 2` folds over the list K translated to the exact
  `Source.Ty` copies. On inputs [t,q], original equalityTest(t,literal
  code σ) selects lifted Hσ(q) in a match and the rest otherwise; the empty
  case is constant output 0. Duplicates safely select literally identical
  Hσ, after injectivity of the frozen code. All branches preserve the
  input q, independent of its original context and lexical status.
* Use the accepted actual predecessor, equalityTest, and chosen constant
  AST: `InternalEqualityTestDefinitions` and
  `InternalFixedWindowVertexDispatchDefinitions.constant`, with their
  publicly proved behavior. `branch`, `conjunction`, the zero and
  projection inputs are the existing literal Program constructors.

## Frozen interfaces and closure order

1. **Original result-type support, all raw:** for fixed original S,K and
   every raw t,q, typed(fixed S K,t,q)=true implies
   ∃ ρ ∈ original K, t=code(formulaType ρ). Use
   `ExactScalarAddress`, `ExactAddressView`, identical literal
   `decodeAddress` data, and `finiteWindowBit` of the canonical
   representative. The latter gives `typedBit` and actual
   `support Q`; `rootSupport Q` gives membership for Q.type,
   which equals the address result. `ExactFormulaTypeCoding` identifies
   the literal type code. No conclusion about all contextual entries or
   all global source types. Choose corpus map and inverse explicitly;
   derive code injectivity from the original decode/encode pair. Closed K
   transports to right-child membership for every admitted arrow type.
2. **External numerical calibration:** evaluate Hτ([q]) =
   (typed s (typeCode τ) q).toNat for **every** raw q, by external Ty
   recursion and the actual calibration of the four leaves. If original
   typed is false, its conjunct forces zero regardless of all cold branch
   computations. If true at an arrow, #613 supplies actual u and v
   with probe=some u, graph=true, typed codomain true; graph's exact
   definition (application == some v) identifies the literal A option
   output. Thus the chosen h preserves original typed for **every** raw
   [t,q], including outside-window and malformed t,q (excluded only by
   exact result-type support, not by implicit admission).
3. **Internal dispatch:** for any original body, α, Γ and arbitrary open
   q, show the actual graph of the chosen h at the literal type numeral
   is interderivable with the actual graph of its Hτ branch (all outputs
   or at least the original exact one). For nonmember τ, prove that the
   **same** graph has output zero on arbitrary q; accepting it yields
   contradiction by functionhood and successor-not-zero. Branch tests
   have only literal closed numeral operands. Derive their exact operand
   graphs via constant/projection calculus and the object closed-numeral
   evaluation theorem for the particular original equalityTest AST.
   This allows a finite List induction in Lean, using actual branch graph
   inversion/introduction in each object derivation, **not** truth
   reflection or standard model entailment. q is never specialized
   or evaluated.
4. **Internal arrow branch:** from an arbitrary-open derivation that
   H(σ→τ)(q) accepts, eliminate exact conjunction. Case-split the actual
   graph output of a; the zero case yields zero for that branch and
   contradiction. Under suc(u), original predecessorSuccessor and
   compositionRecover align the actual interior with [q,u]. Repeat
   for A: the zero branch contradicts acceptance; under suc(v),
   predecessorSuccessor and compositionRecover align its interior with
   [q,u,v]. Recover the actual p accept and Hτ graph at v.
   Using (3) and K-closure, convert Hτ to **the same** chosen h's typedAt
   at literal codomain, not a weaker unrelated verifier. Use genuine
   ∃ introduction/elimination and syntax-preserving relabeling to build
   precisely `witnesses p h a τ q`, with the exact fresh q/u/v
   graph. Option zero cannot be accepted as an address.
5. **Selection/coherence:** package chosen h with proof of its original
   all-code valuation (so #614 & any numerical checks can be freshly
   instantiated), actual `TypedProbeTotal d p h a c` at every d,c,
   and exact supplied selected p and a calibration unmodified. Use
   accepted original program-existence theorems and the #596 package
   to remove any *new* introduced premise, while preserving its
   actual i,j,r,d,p selection. Carry h into the future numbered assembly
   explicitly; do not assert object equivalence to arbitrary older h0
   merely from equal standard-natural values.

## Nonclaims and separate blockers

The successful fresh variable is not thereby computable at every type:
that requires actual object neutral closure and the Bottom/function-side
direct-step decomposition, and still needs an open positive path/source
bridge. #609/#612 remain external numerical facts, not admissible object
rules. Arbitrary-free-term matching is another author lane. No proof here
uses it silently. No general cutoff or fuel is introduced by finite
dispatch; every type outside the genuine fixed K is rejected by original
typedness and checked literal dispatch, not excluded from the target.
