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
