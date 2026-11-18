# Paper 17 source-exact port

Source: `17-permitted-control-canonical-comparison`, from manuscript commit
`17377d6d02d20b26b0cf34ab50bb9d52d7c32305`. New proofs live in
`LogicLineages.PermittedControl`; earlier standard-control code is unchanged.

## First frozen component

`Definitions.lean` retains the literal hierarchy by definitional reuse of
`OrdinalComparison.Phi = fastControl 5 (n+100)`; the underlying recursion is
exactly F0(n)=2^n and F(j+1)(n)=Fj^[n+1](n).
`initialLcm` is lcm(1,...,n), starting at 1. `correction` uses integer
least-nonnegative remainder and then a justified conversion to Nat. Natural
truncated subtraction in that numerator would be wrong, particularly at n=0,1.
`nearControl b` preserves exactly [0,b].

The two independent frozen targets are the numerical prefix/distance/evenness/
one-step-modular bundle of `lem:control` and the unbounded count identity
`eq:orbit-potential`. They do not assume a modular supplier: both refer to the
literal newly defined near control. The modulus and iteration count remain
arbitrary. Existing old `Control` arithmetic can supply n<G(n) and iteration
monotonicity because these are about the same literal G, not a new control.

Not included: f* factorial control, the bound by 2n!, double-exponential
separation, primitive recursiveness, eventual hierarchy bound, or any full
numbered theorem. These remain explicit obligations.

## Subsequent dependency order

1. Complete both explicit-control growth/effectivity results at their literal
   definitions, including the prefix-to-tail transition.
2. Parameterize actual epsilon-zero norm-bounded collapse and its greedy
   predecessor recurrence by the new control, proving rather than assuming
   each needed property. Old `ActualCollapseDefinitions.actualCollapse`,
   `ActualDescentDefinitions.actualDescentStep`, and
   `ActualTerminalDefinitions.actualTerminalData` hard-code Phi. They cannot
   be reused by merely renaming Phi or claiming selected-control equality.
   The norm and maximum-predecessor definitions have independent reusable
   mathematical content, subject to source and closure verification.
3. Prove the actual visit to omega^2 and the exact funnel event-count formula.
   Only then combine the unbounded potential with it for `thm:counts`.
4. Prove actual interval entry existence/finite-tail versus long-entry
   cases, then `prop:entry-residues` with its stated effective tail.
5. Port entry propagation, gaps, equal-gap certificates, inverse thresholds,
   and the finite normalization/closed-block arithmetic decision. Preserve
   ordered inputs, domain guards, and effective witnesses; a supplied
   decision oracle is not the closed-block theorem.
6. Match the literal parsing-policy source interface and full ground-free
   source translation, then assemble the positive main theorem. Internal
   types, recursors and finite nesting remain unrestricted.
7. Match the existing weak/strict functional-input hardness route separately;
   distinguish finite-query internal-level-two and single-query level-three.

The unchanged displayed control's unrestricted all-ground problem is not
settled by this paper's selected-control theorem. Equality hardness for
functional inputs and free-parameter quantifier elimination are not asserted.

## Verification

Freeze definitions/targets and source hashes before candidate proofs. Compile
only through the existing serialized checker with the unchanged resource
profile, after the coordinator grants its queue. Then exact alias/axiom checks,
source-correspondence review and recursive evidence reconciliation precede any
acceptance. No full-build or new numbered-count claim follows from these
supporting checks.

## Next numerical/effectivity split

The frozen `NearControlGrowth` target adds the actual near-control growth and
finite-level bound, not an assumed growth class. A prospective effectivity
proof will use a bounded greatest-common-divisor search to certify `Nat.lcm`,
primitive recursion for `initialLcm`, and a proved nonnegative natural-residue
implementation of the existing integer correction. This does not replace its
semantics: equality to the original integer remainder must be proved before
transporting a primitive-recursive certificate. The explicit factorial control
will require its own definition and proof, and remains unpaid until then.

## Native milestone: near-control numerical/effectivity endpoints

`GrowthStatementChecks` passed native check receipt
`1794976532193944335-2`; recursive evidence validates 9 source-matched modules.
`EffectivityStatementChecks` passed native check receipt
`1794976562750071759-2`; recursive evidence validates 11 source-matched modules.
Both exact target aliases have only propext/Classical.choice/Quot.sound.
The first failed proof drafts and receipts are retained. Repairs changed only
proof elaboration (explicit implicit arguments, a cast simp lemma, and the
predicate supplied to bounded greatest-search); frozen targets/definitions
were not changed. Independent final review requested from evidence_review.

Thus the near-control numerical branch now has checked all-input growth,
strict next-G bound, explicit eventual F6 bound, evenness, majorization,
primitive recursion (joint in b,n), and arbitrary-orbit modular decrement.
This still does not cover factorial control, complete descent counts, entry
residues, canonical assignments, or the paper's comparison main theorem.

## Next factorial-control source-exact scope

Use a separate definition file so the already frozen near-control definition
file stays byte-for-byte intact. Define fStar n = (G n)! + 2*p(n) - 2 in Nat,
then prove the pre-subtraction expression is at least 2 to certify that its
cast agrees with the source integer expression. Include n=0 and n=1 rather
than starting on an artificial positive-input tail. The freeze should require
actual primitive recursion, evenness, G-majorization, fStar<=2*(G!), the exact
double-exponential step, strict fStar<G(n+1), eventual F6 and potential
modulo m for all m>=1,n>=m. Arbitrary-orbit decrement uses proven majorization
to keep the orbit inside this tail, not a supplied invariance hypothesis.

Reuse bounded factorial recurrence and the existing G growth lemmas. For
modular decrement prove 2*m divides (G n)! when m<=n using 2*m<=G n;
transport through the exact integer cast and divide even quantities by two.
For growth prove a factorial upper bound below a double tower, then obtain
four successive exponentiations below F4(G n+1). These estimates must be
proved, not installed as assumptions in the final interface. Near-control
results do not discharge any fStar obligation by renaming.

## Full lemma assembly comparator

`ControlTargets.lean` freezes `FullControl`, requiring the literal laws for
`factorialControl, B=0` and each `nearControl b, B=b+1`. It includes all seven
source clauses rather than merely taking a supplied control-law hypothesis.
`UniformFiniteLevel` additionally requires one common finite hierarchy level
and threshold across both actual controls and every b. The intended witnesses
are level 6 and threshold 101, already proved for near-control and included in
the factorial branch's frozen proof obligation. The final assembly may be
accepted as lem:control only after the factorial native/evidence/final review
and full assembly source correspondence all pass. No comparison theorem or
complete descent/entry residue result follows merely from these numerical laws.
