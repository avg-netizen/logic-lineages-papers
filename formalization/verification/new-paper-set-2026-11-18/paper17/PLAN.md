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

## Factorial and complete numerical lemma native milestone

Native receipt `1794976902194327090-2` passes both FactorialStatementChecks
and ControlStatementChecks. The combined recursive evidence report validates
19 local modules and four exact aliases with standard-only foundations.
One failed draft and receipt are preserved: the sole failure was a missing
Int namespace on dvd_add; repair also made addition association explicit.
Frozen definitions, targets, and source pins remain unchanged.

The full actual two-control numerical lemma is now native-proved, including
joint near-control primitive recursion, source-exact factorial subtraction,
all-input evenness/majorization/growth/strict upper bounds, literal potential
thresholds, and a uniform level-6 eventual bound. Both arbitrary-orbit
identities are proved without assumptions about orbit invariance. Independent
final review is requested before any numbered register promotion. Complete
ordinal descent counts and all later comparison statements remain pending.

## Actual parametric collapse native milestone

`CollapseStatementChecks` passed receipt `1794977757928919751-2`.
Recursive evidence validates all 59 current-source local modules and five
standard-only exact aliases. Full generic estimates and limit-part recurrence
are instantiated without remaining law premises at both actual selected
controls. The stronger printed finite-tail lower bound is included.
The first failed draft/receipt is retained; the only repair replaced a
commutative-style add-monotonicity lemma with ordinal-specific strict addition
cancellation. Frozen target/definitions unchanged. Independent final review
requested before promotion of either printed statement. Queue released.

The next effective-evaluator plan is separately documented and reviewed in
EFFECTIVE-EVALUATOR-PLAN.md and its review. It requires actual least search
count equality, all-input totality including invalid codes, actual Computable
output and denotation agreement. Generic per-function computability is not
higher-order index uniformity; joint-b computability must be specified if
claimed. No effective evaluator theorem is obtained from this semantic gate.

## Genuine effective evaluator native milestone

`EvaluatorStatementChecks` passed receipt `1794978194757150683-2`.
Current-source recursive evidence validates 93 modules and both exact aliases
with only standard foundations. This is not a semantic-only result: arbitrary
per-function Computable f with source numerical hypotheses yields a concrete
Partrec search program, all-input totality, Computable total output, membership
of the actual first-finite event count in the least search, actual endpoint
agreement and independent collapseWith denotation. Both selected controls are
instantiated with no remaining admissibility or computational premise.
Actual terminal identities include the norm orbit and 0<D<Z.

One initial failed draft/receipt is preserved. Repair added definitional rfl
after unfolding the well-founded recursion and explicit pair projections;
frozen definitions/targets unchanged. Independent final review requested for
cor:closed-evaluation promotion. No higher-order index uniformity, joint-b
computability, optimized M/L recursion or later residue theorem is asserted.

## Count/entry route: earliest finite-coefficient dependency

The next frozen packet is the complete printed cor:finite-coefficient and
supporting exact terminal count/endpoint on omega*k+n, all k,n including0.
ActualFiniteHeadNorm and ActualFiniteHeadMaximum are control-independent.
SmallKernelSuppliers proves actualControlledCount g (omega*k+n)=k for every
expansive g, with the literal limit-part maximum step and actual well-founded
count. Prove its equality to the second projection of terminalWith f by actual
ordinal induction; do not identify it by name alone. Then the checked terminal
norm orbit and collapse decomposition give the complete printed identity.
Concrete factorial and near-control clauses have no remaining law premise.
This pays no high-head residue, funnel, entry or comparison obligation yet.

## Complete count residue native milestone

CountStatementChecks passed receipt1794978972810649548-2. Recursive evidence
validates120 current-source local modules and three standard-only exact aliases.
The actual ordinal induction proves the omega-squared limit-part visit and
exact funnel count; no funnel premise is supplied. The actual terminal orbit
then proves both high-head and linear-head D/Z/J residues at the exact source
threshold, plus the literal period-2m residue table for every selected control.
Two failed drafts/receipts are retained. Repairs concern ordinal power
normalization, cast-zero normalization and explicit universe0 annotations in
proofs only; frozen target/definition pins unchanged. Independent final review
requested before thm:counts promotion. Entries/main comparison remain unpaid.

## Actual first-entry foundation verified, long-residue candidate drafted

EntryFoundationStatementChecks passed receipt1794979790319015497-2, with
142-module recursive evidence and independent supporting-only final approval.
It proves the genuine partial first-hit iff/Partrec contract including skipped
positive targets and the finite-absorption distinction, plus source-exact
affordable-tail existence and norm orbit. No full entry-residue promotion from
that foundation alone. Failed proof drafts/receipts are preserved.

The subsequent full residue candidate uses the true ordinary-ordinal split
nu=P+omega*j with omega² dividing P and Nnu=NP+2j. Generic actual prefix trace
proves finite-omega-tail first-entry count k. In the long case, an actual
ordinal induction at barrier P+omega² forces the first-hit count residue:
the barrier maximum is P+omega*floor((b-NP)/2)+(b-NP)%2. Evenness of b retains
the odd-prefix correction through ceil(Nnu/2). Above the barrier, the target
barrier is affordable; the one-step potential transports the induction.
The exact norm residue then follows from the already-proved actual entry
orbit, not from a supplied entry-residue oracle. Full candidate awaits native
checks and independent final review; no further source status is claimed yet.

## Full actual entry residue native milestone

EntryStatementChecks passed receipt1794980191164335688-2; current recursive
evidence validates150 modules and three standard-only exact aliases. The full
source entry proposition is now proved in Lean for both selected controls,
including exact finite-tail count, complementary long-interval signed residues,
ceil(Nnu/2) for odd prefixes, explicit source threshold, real first-hit witness
and norm orbit. The genuine partial computability/first-hit iff and affordable
existence gates are included. Actual prefix decomposition and shifted-barrier
induction provide the mathematics; no entry residue or suffix-kernel oracle
is supplied. Two native-failure drafts/receipts retained, with proof-only
ordinal numeral/cast simplification repairs. Frozen target/definitions remain
unchanged. Independent final review requested before numbered promotion.
Subsequent full table families, relative comparison and arithmetic/main theorem
are separate obligations.

## Displayed table native milestone

EntryTableStatementChecks passed receipt1794980637989197722-2; recursive
current-source evidence validates151 modules and three standard-only aliases.
All four table rows, both interval classes, positive bare iterates, and the
actual zero-event identity interval with its literal odd input are included.
The single failed draft/receipt is retained; two max-tail omega proof terms
were replaced with direct order-transitivity proofs. Frozen pins unchanged.
Independent final review requested; this is supporting-only, not an arithmetic
or comparison solver result.

## Next comparison dependency

Prove the actual ordinary-addition relative norm identity and concrete CNF
prefix-cost bounds before defining relative maxima or claiming propagation.
Natural-sum additivity and existing compatible-prefix norm addition do not
cover arbitrary absorbed suffixes. The source shift retains all prefix terms
whose exponents are at least the incoming leading exponent, including equal
boundary exponents; zero relative state uses full N(mu) separately. Actual
relative max/evaluator bridging must use this exact cost, not a supplied
profile oracle or assumed equality with an unchanged-G assignment.

## Ordinary relative norm milestone

RelativeNormStatementChecks passed native receipt1794981189487204709-2 under
unchanged standard caps. Both exact aliases have standard-only axiom closures;
recursive current-source evidence covers60 modules. Independent final review
approved supporting scope only. Complete filtered actual CNF prefix, retained
norm/bounds, zero convention and unrestricted ordinary-addition absorption
identity are paid. No source profile compatibility assumption is left open.
One failed proof draft and receipt preserved; frozen targets unchanged.

Next: RelativeDescent definitions/targets/source map frozen before proof, exact
pre-scope requested. Actual maximum subtraction and literal relative entry
recursion (including selected controls, genuine hit existence and first finite)
remain pending. Propagation and all later comparison/arithmetic remain pending.
