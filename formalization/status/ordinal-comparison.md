# Ordinal and comparison formalization

Owner: `formalize_ordinals`. Scope: papers 04–10. Root owns package configuration,
the global target register, build runner and acceptance gates. This file is the
lane's local checkpoint; it does not resume mathematical frontier research.

## Authorized external continuation — 2026-10-29 16:45 UTC

The historical local-worker pause below remains in force for those workers.
This section records the separately authorized external continuation; it does
not restart the private/local automation. The central build steward alone ran
Lean through `scripts/check.py`; root and the independent source auditor own
freezes, acceptance ledgers and publication. Existing accepted semantics and
calculator files were preserved.

The initial representation, natural-arithmetic and finite-tail candidates now
pass their exact gates after compiler-directed repairs. Additional source-domain
proofs define the norm by actual-ordinal hereditary-CNF recursion and the maximum
and unary collapse independently on actual ordinals, then prove their explicit
notation correspondences. There is no hidden correctness premise or replacement
of ordinary ordinal operations by natural arithmetic.

| Newly checked scope | Central receipt in `build-reports/` |
|---|---|
| Epsilon-zero calibration; representation soundness and completeness | `1793266656163446923-6.json` |
| Natural-sum coefficients, norm additivity and actual denotation | `1793268922711366793-6.json` |
| Natural-product actual denotation and norm bound | `1793269134898389121-6.json` |
| Notation finite tails and limit maximum saturation/strict growth | `1793269461891094579-6.json` |
| Actual CNF exponent descent and positive finite coefficients | `1793271118285845628-6.json` |
| Actual-CNF norm equation, below-epsilon-zero uniqueness, notation correspondence | `1793272663372089230-6.json` |
| All actual-ordinal finite norm balls and exact finite semantic enumerator image | `1793274547086434704-7.json` |
| Independently defined actual maximum: exact greatest specification, uniqueness, notation correspondence | `1793277026322837585-7.json` |
| Full actual source `lem:saturation` (both conclusions) | `1793279023996396169-7.json` |
| Actual unary collapse equation/uniqueness and full `lem:controlled-strictness` (including finite values) | `1793279852531567128-7.json` |
| Full actual source `thm:single-predecessor` | `1793283089630614057-7.json` |
| Actual nonfinite split, strict replacement descent, collapse and norm updates | `1793283720314443438-7.json` |
| First finite replacement endpoint and full `thm:complete-count`, including both strict bounds | `1793284704328308516-6.json` |
| Exact finite-head norm/maximum suppliers and full `cor:finite-head` | `1793285606947394818-6.json` |
| Joint order/norm count-monotonicity suppliers and full `lem:tail-separation`, including injectivity | `1793286378781061472-6.json` |
| Actual norm domination and finite-tail lower bound (cited Proposition 2.3 suppliers) | `1793286664881417460-6.json` |
| Faithful raw ONote/natural pairing codec, both roundtrips, literal equations and explicit normalization primitive-recursion certificate | `1793287385581550202-6.json` |
| Finite-table raw-code treeWeight algorithm: literal equations, exact source-norm agreement and genuine `Nat.Primrec` certificate | `1793292274234536879-6.json` |

All listed gate axiom closures are subsets of `propext`, `Classical.choice`,
`Quot.sound`. Root's acceptance records, exact frozen hashes and fresh aggregate
receipts remain authoritative; a successful focused receipt is not a claim that
an unobserved consolidated build or remote CI passed.

**Encoded effectiveness remains open.** The actual ordinal evaluator is a
well-founded mathematical construction with a proved literal first-finite
trajectory and terminal identities. This is not a Mathlib `Computable`
certificate on a faithful finite input encoding. Consequently the effectiveness
part of `lem:finite-balls` and `cor:closed-evaluation` is not promoted from these
results. The explicit raw `ONote`/natural-number pairing bijection now has both
roundtrips checked, plus faithful explicit `Denumerable`/`Primcodable` structures
(no global instances installed) and a separate `Nat.Primrec` normalization
certificate. The finite-table numeric function `rawNormCode` additionally has
a genuine `Nat.Primrec` proof and exact agreement with the full-multiplicity
`Vendor.R1.treeWeight` on every raw input. These raw-code facts do not supply
normal-form recognition, `NONote` encoding, comparison, finite norm-ball
enumeration, or the encoded evaluator; those computation certificates remain
pending. The optimized simultaneous
maximum-predecessor recursion and the remaining source-assignment/comparator
and papers 06–10 obligations also remain pending.

## Explicit user pause — 2026-10-29 06:17 UTC

The user paused local formalization for an external agent to take over. **This
lane is paused: no proof work, compiler launch, author process or Git operation
is authorized until a later explicit restart.** All edits are preserved. No
lane-owned compiler or author remains live; the last actual invocation exited
with diagnostics, and later attempts were prelaunch memory deferrals. Root owns
the separate shared author/native-process shutdown; this is not a claim about
another process namespace.

### Accepted handoff

[ACCEPTED-COMPONENTS.json](../LogicLineages/OrdinalComparison/ACCEPTED-COMPONENTS.json)
is the exact public ledger: **15 gates, one complete numbered manuscript lemma**.
It pins target, gate, proof, semantic and manuscript SHA-256 values. A separate
integrity read verified all 28 distinct pinned files. Accepted source files were
not changed while drafting the pending extensions.

| Accepted scope | Receipt in `formalization/build-reports/` |
|---|---|
| Entire paper 05 `lem:phi-growth`: literal F0=2^n, iterated hierarchy/shift, encoded Computable/Primrec, strict growth, double tower and final linear gap | `1793247538850699184-2.json` |
| Every normal-notation finite norm ball and exact constructive-enumerator membership | `1793248381898355174-2.json` |
| Actual norm-controlled finite-max collapse, independent universal equation, uniqueness, finite values and norm domination; actual greatest predecessor and finite min formula | `1793249398256550687-2.json` |
| Five typed-source prerequisites: arity level, subtype-closure transitivity, renaming identity/composition, substitution identity | `1793250218115478637-2.json` |
| Complete selected calculator Ordinal/ArithmeticBounds/Norm closure in modern module mode; original calculator frozen | `1793247684146440534-2.json` |

Every accepted closure uses a subset of `propext`, `Classical.choice`, `Quot.sound`.
Normal-notation facts do not yet certify the full actual-ordinal manuscript
quantifiers; the finite-ball components do not complete natural arithmetic or
the optimized maximum-predecessor recursion. Typed-kernel facts do not replace
named-source correspondence or any termination-comparator theorem.

### Exact pending state and first restart checks

1. **Representation:** `OrdinalRepresentationTargets`, `EpsilonZeroCalibration`
   and `OrdinalRepresentationSound` compiled in receipt
   `1793251626773742328-2.json`. The only reported completeness error was the
   ambiguous field notation for `NF.below_of_lt'`. It is already repaired to
   `refine ONote.NF.below_of_lt' ?_ t.2`. The earlier unconstrained universe was
   already repaired to explicit `Ordinal.{0}`, matching NONote. The repaired
   completeness/gate has **not run**: the next attempt deferred at 965 MiB
   before launch, receipt `1793251905280532583-2.json`.
   After an explicit restart, first run from `formalization/`:
   `python3 scripts/check.py LogicLineages/OrdinalComparison/OrdinalRepresentationStatementChecks.lean`.
2. **Natural arithmetic:** `NaturalSum*`, `NaturalArithmeticDefinitions/Targets`,
   `NaturalProduct*` are complete-looking **uncompiled candidates**, with no
   claimed pass or source theorem acceptance. Sum implements sorted CNF merging;
   its targets include actual Mathlib ordinal coefficients and equality to the
   source operation defined by collecting actual CNF coefficients. Product
   implements paired monomials, has normality/norm-bound candidates, and an
   actual-CNF interpretation candidate. Its gate requires both denotation and
   the norm bound. Next checks, after representation and peer release:
   `python3 scripts/check.py LogicLineages/OrdinalComparison/NaturalSumStatementChecks.lean`,
   then `python3 scripts/check.py LogicLineages/OrdinalComparison/NaturalProductStatementChecks.lean`.
   No actual natural-sum/product diagnostic has been collected yet.
3. **Other preserved candidates:** finite tails/limit saturation remain
   uncompiled (`FiniteTail*`, `LimitPredecessor*`). The known duplicate-binder
   field-call issue was also repaired explicitly in FiniteTail. CoreControl
   fallback files are unused, uncompiled, and not accepted surrogates for the
   original numerical target. Source substitution composition, reduction
   transport, named-source correspondence, canonical assignments, optimized
   predecessor/evaluator/count results and papers 06–10 full targets remain open.

Only the shared `scripts/check.py` may launch Lean: no concurrent Lake/native
builds or cold Mathlib rebuilds. Mathlib gates retain the default guards; the
strict core-only profile is valid only after verified Init/Lean/Std import
closure. The recent core kernel pass used that profile legitimately after
removing a wholly unused iteration import, with mathematical bodies unchanged;
[SOURCE-KERNEL-ADAPTATIONS.json](../LogicLineages/OrdinalComparison/SOURCE-KERNEL-ADAPTATIONS.json)
records it. Do not fit an actual-ordinal statement to that profile by changing
its semantics. Root measured real page-I/O waits and memory deferrals; these
are separate from proof diagnostics. Do not replay unchanged resource failures
or independently raise guards.

### Material outside the papers repository

No accepted result requires a private import. The selected three-file norm
closure, its full local dependencies and provenance are already public here.
For optional later reuse, the sibling 3.1.3 tree is
`projects/inverse/alexander-open-problems-results/alexander-dissertation-lean/`:

- `Alexander313/Wilken/AdditiveNormalForm.lean` concerns **ordinary** ordinal
  addition with absorption; it does not supply natural-sum additivity.
- `Alexander313/Wilken/FiniteCollapse.lean` is the hull/minimum/cardinal-fallback
  construction of a different Wilken definition; it does not supply this
  natural-valued norm-controlled collapse.
- `Alexander313/Carlson/{Basic,Patterns,Semantics,Core}.lean` and the wider
  Carlson directory may help beyond the finite material already adapted by
  the public calculator. Some older modules are uncompiled or conditional:
  inspect exact statements, dependencies and axioms before selecting reuse;
  do not import the aggregate as a certified supplier. Copy every needed local
  source publicly with hashes before accepting a reused result.

For mathematical suppliers still requiring actual proofs, exact bibliographic
selectors are already in the public papers' `SOURCES.md`/`references.tex`:
Wilken–Weiermann (2012) literal T/assignment/domain/norm theorems; Kop (2012)
strong-pair/auxiliary reduction; Pohlers (2009) ID1 stages/height; Simmons
(2004, 2008) calibrated extractor; Snyatkov first-order arithmetic decision;
Narendran/Dong polynomial-semiring hardness. A citation is not an assumed Lean
supplier. Additional text/material remains in the private sibling project:

- `projects/inverse/logic-lineages/collected-papers/`, including
  `text/2009-pohlers-proof-theory-the-first-step-into-impredicativity.txt`.
- `projects/inverse/logic-lineages/external-results/2026-10-23-cumulative-ii5/`,
  especially `reviews/simmons-primary/SOURCE-READ-RECORD.json` and
  `ordering/SIMMONS-SOURCE-AUDIT-UPDATE.json`.
- `projects/inverse/logic-lineages/external-results/2026-10-27-wilken-weiermann-exposition/`
  contains the earlier exposition and source/arithmetic/comparison reviews.

Read the full public TeX closure: paper 05 includes `foundations.tex`; paper 09
also includes `source-realization.tex` and `hardness.tex`. The detailed source
scope and unpaid supplier plan follow below. This handoff is an inventory,
**not an instruction to resume**.

## Current checkpoint

**The complete source elementary-control lemma now compiles and passes its
axiom audit.** `ElementaryControlStatementChecks.lean` proves paper 05,
`foundations.tex`, `lem:phi-growth`, against the separately authored target:
actual encoded `Computable Phi`, strict monotonicity, domination of the identity,
the whole-domain double-tower inequality and the final `4*Phi(n)+4` strict gap.
Its additional fixed-level primitive-recursive certificate uses Mathlib's real
`Primrec` predicate. Both gate closures use only `propext`, `Classical.choice`,
and `Quot.sound`. Receipt: `build-reports/1793247538850699184-2.json`.
This completes that lemma, not paper 05 as a whole.

The earlier exact numeric gate additionally checks the literal exponential base,
input-dependent iteration, shift by 100 and the stronger exponential lower bound;
receipt `build-reports/1793246525082573003-2.json`. No concrete large control value
is evaluated. The full source target has SHA-256
`bd94b0ade60cc7242c5321012d445a1e003e669206a1c7e5a57e3e8e55ce33dd`.

The earlier legacy-module import attempts reached the wall bound before theorem
diagnostics, including receipt `build-reports/1793244559343130747-2.json`.
Root diagnosed that pinned Lean loads private imported payloads for legacy roots.
The current owned closure now uses `module`, `public import`, and explicit public
sections. An explicit standard Nat import supplies the exported order instance
needed by the unchanged numerical target. The original calculator remains
frozen. Its selected complete three-file norm dependency closure has been
adapted under [Vendor/R1](../LogicLineages/OrdinalComparison/Vendor/R1/README.md),
with source hashes and reverse-normalization body equality recorded there.
The complete modern vendor closure now **compiles** without changing any copied
mathematical proof body: receipt `build-reports/1793247684146440534-2.json`, peak
791,472 KiB. The wrapper then deferred at its unchanged available-memory gate
(953 MiB versus 1,024 required) before compiling the ordinal shim. A later
attempt compiled `Definitions` and the independent `Targets`, then found two
local norm-ball proof diagnostics; receipt
`build-reports/1793248101061166852-2.json`. The repairs use explicit natural
subtraction cancellation and the exact subtype membership theorem. The repaired
`NormBallStatementChecks.lean` now **passes** both independent finiteness and
exact-enumerator gates, with only the standard three axioms; receipt
`build-reports/1793248381898355174-2.json`. This proves the normal-notation
finite-ball components, not the whole source natural-arithmetic lemma.
The existing collapse and greatest-predecessor candidates now also **pass**
their independent gates; receipt
`build-reports/1793249398256550687-2.json`, peak 772,608 KiB. The actual
well-founded finite maximum satisfies the universal predecessor specification,
is unique, has exact finite values and dominates the tree norm. The exhaustive
greatest-predecessor implementation and its exact finite `min` formula pass as
well. Both namespace audits contain only the standard three axioms. The
controlled-bound proof uses a typed finite supremum to avoid over-reduction;
no heartbeat or resource cap was raised. These are normal-notation components;
the actual-ordinal representation supplier is still missing.

[ACCEPTED-COMPONENTS.json](../LogicLineages/OrdinalComparison/ACCEPTED-COMPONENTS.json)
records the fifteen accepted component gates, exact types, source scopes and target,
proof, semantic and manuscript SHA-256 pins. Only `lem:phi-growth` is recorded as
a complete numbered manuscript lemma. The other accepted facts do not silently
complete natural arithmetic, the optimized maximum recursion, or all-ordinal
quantification.

Root's runner now separates a 180-second wall allowance from the unchanged
90-second CPU allowance, with a 1,536 MiB managed heap, unchanged 1 GiB actual
RSS cap, and a 1 GiB prelaunch available-memory gate. There are no legacy import
retries or independent cap overrides. This lane released its native slot to the
models/algebra gate and main-thread RL gate after the numerical checkpoint.

- [Control definitions](../LogicLineages/OrdinalComparison/ControlDefinitions.lean) fixes the exact
  hierarchy `F₀(n)=2^n`, `Fⱼ₊₁(n)=Fⱼ^[n+1](n)` and `Phi(n)=F₅(n+100)`.
- [Independent targets](../LogicLineages/OrdinalComparison/Targets.lean) states the
  finite normal-notation norm-ball component, an exact enumerator interface and
  the whole-domain numerical control growth component. It imports no new proof
  implementation and assumes no inhabitant of any target.
- [Norm-ball proofs](../LogicLineages/OrdinalComparison/NormBalls.lean) give a
  structurally recursive finite enumeration of all raw hereditary notations of
  bounded additive norm, then filter normal forms. Membership completeness is
  proved by induction on the norm bound; finiteness and the exact normal-input
  enumeration are consequences.
- [Control proofs](../LogicLineages/OrdinalComparison/Control.lean) prove
  inflation, strict monotonicity, monotonicity in hierarchy level, exponential
  lower bounds and the stronger gap
  `2^(2^(Phi(n)+1)) ≤ Phi(n+1)`. No concrete large control value is evaluated.

The current independent statement snapshot is:

| File | SHA-256 |
|---|---|
| `ControlDefinitions.lean` | `67b885bc02dc1ebc0322f46bc4607c5e41e15c74b8957976986541cc23a04ee4` |
| `ControlTargets.lean` | `2b5c663880aec5f55fe6f526bacf19ce131d3ae77e9485332b78dc5826d693c7` |
| `Definitions.lean` | `d3a62bbfa4141166fbdf5f5bcc3f3e7e8ecad7c437a15ce5df9baff851a67867` |
| `Targets.lean` | `e3d2625728df7aa38f54c8639d98959ee15c097a1f88d08f4b8921b58516afbe` |
| `CollapseTargets.lean` | `6b9963e757519a2115f764db6cefe8527d76d1695d47fa93e165942c6f9655e6` |
| `PredecessorTargets.lean` | `c0fc975080cd34cd6296a53fad842c237d223f35d650b1a2bce060dc19ce4733` |
| `ComputabilityTargets.lean` | `55aed55d9cc6faef4ec369d770530e14bfe2efd9c19beab581cfe2a540d1cc2f` |
| `ElementaryControlTargets.lean` | `bd94b0ade60cc7242c5321012d445a1e003e669206a1c7e5a57e3e8e55ce33dd` |

The first import-loading investigation split numerical definitions and their
statement away from the broad ordinal import without changing their formulas
or declaration names. No target had been accepted before that split. The
additional core-Nat-only companion target/proof candidates preserve the same
inequalities with monotonicity expanded, but are uncompiled and are not needed
for the original Mathlib target gates.

[FiniteCollapse](../LogicLineages/OrdinalComparison/FiniteCollapse.lean)
constructs the literal norm-controlled finite maximum by actual ordinal
well-founded recursion and proves its separate specification, uniqueness,
finite values and norm lower bound. The independent
[collapse statement](../LogicLineages/OrdinalComparison/CollapseTargets.lean)
quantifies over all normal predecessors and was written before the implementation.
[MaximumPredecessor](../LogicLineages/OrdinalComparison/MaximumPredecessor.lean)
proves the exhaustive greatest-predecessor and exact finite-case formulas
against its separate target. Both sets of exact gates now compile and audit.
Neither construction assumes a collapse/predecessor correctness supplier.

Neither of these component targets is the full foundations paper. In particular,
the paper's finite-ball lemma additionally asserts natural-sum/product algorithms
and norm additivity. Its complete control lemma additionally asserts encoded
computability and the final linear-gap consequence. The independent
`ElementaryControlTargets.lean` and separate implementation/check files now
**compile and audit for that entire source statement**.
An executable Lean definition will be kept distinct from an explicit encoded
machine computability theorem where that stronger statement is required.

[NaturalSumTargets](../LogicLineages/OrdinalComparison/NaturalSumTargets.lean)
now independently specifies natural sum by top-level Cantor coefficients and
states exact additive norm preservation. The separate
[NaturalSum](../LogicLineages/OrdinalComparison/NaturalSum.lean) candidate merges
the whole normal-form lists, retains lesser monomials and combines equal
exponents. Its candidate proofs cover coefficient addition, normality and norm
additivity. These files are **uncompiled**.
The coefficient specification is the source's collection-of-monomials
definition, not a renaming of ordinary ordinal addition.
The additional `NaturalSumDenotationTargets.lean` fixes the external gate in
Mathlib's actual ordinal Cantor coefficients for every ordinal exponent. That
bridge now has a separate **uncompiled** candidate implementation in
`NaturalSumDenotation.lean`; the syntactic invariant alone will not be reported
as the whole source natural-sum theorem.

`NaturalArithmeticDefinitions.lean` now fixes the actual ordinal operations
directly by Cantor coefficients and paired monomials, independently of the
notation algorithms. Its separate targets demand denotation equality and the
product norm bound. `NaturalSumInterpretation.lean` has the candidate sum bridge
using actual coefficient equality and Mathlib's `CNF.eval_coeff`.
`NaturalProduct.lean` implements the literal paired-monomial merge, with pending
normality and norm-bound proofs; `NaturalProductInterpretation.lean` has the
pending actual-Cantor-coefficient proof chain. The product gate requires both
denotation and the norm bound. **None of these arithmetic gates has passed**;
no correctness supplier or encoded-computability certificate is assumed.

`FiniteTailTargets.lean` and its separate **uncompiled** implementation specify
and construct genuine ordinal finite tails with exact norm `N(a+n)=N(a)+n`.
This is a prerequisite of the source limit-saturation argument.
`LimitPredecessorTargets.lean` now states exact saturation and strict budget
growth using `Order.IsSuccLimit` of the actual ordinal denotation. Its separate
proof/check candidates implement the source's finite-successor contradiction;
they are also **uncompiled**. The single-predecessor evaluator theorem remains
pending. These notation-domain components still require the explicit
all-ordinals-below-epsilon-zero representation bridge for the paper's full
ordinal quantification.
`OrdinalRepresentationTargets.lean` states soundness, completeness and the
least-fixed-point calibration explicitly. Its epsilon zero uses Mathlib's
actual next-fixed-point construction. Separate **uncompiled** proof candidates
now cover calibration, soundness and completeness. Soundness uses closure under
omega power, finite multiplication and addition below the fixed point.
Completeness uses actual ordinal induction, the strictly smaller leading log,
positive finite quotient and strictly smaller Cantor remainder. None of the
three pending obligations is assumed. The most recent natural-sum/representation
attempt deferred before any compiler launch at the available-memory gate;
receipt `build-reports/1793249798456336556-2.json` (1,000 MiB versus 1,024 required).
After headroom recovered, target elaboration found an unconstrained universe
in the standalone least-fixed-point clause; receipt
`build-reports/1793250409418692550-2.json`. The definition now explicitly uses
`Ordinal.{0}`, matching Mathlib's `NONote` interpretation. That header repair
is saved; its follow-up default-profile attempt deferred before launch at
988 MiB (`build-reports/1793251043888595578-2.json`). No Mathlib guard or intended
mathematical domain was weakened.

The typed source kernel and five independent structural gates now **compile
and audit**: ground-arity level, subtype-closure transitivity, identity and
composition of renaming, and identity of simultaneous substitution. Receipt
`build-reports/1793250218115478637-2.json`; maximum actual RSS 389,908 KiB.
Their axiom closures are subsets of `propext` and `Quot.sound`.
The strict core-only profile verified every transitive import was Init/Lean/Std,
then enforced its tighter 512 MiB RSS and 768 MiB prelaunch memory guard. A
wholly unused Mathlib iteration import was removed without changing mathematical
bodies; [SOURCE-KERNEL-ADAPTATIONS.json](../LogicLineages/OrdinalComparison/SOURCE-KERNEL-ADAPTATIONS.json)
records that and the reserved-binder/explicit-polymorphism parser repairs.
The implementation uses typed de Bruijn variables and literal curried constants.
The correspondence to the paper's named source syntax, substitution composition,
reduction preservation and termination comparator remain pending. These five
accepted formalization prerequisites are not numbered manuscript theorems.

## Source closure and dependency plan

The seven papers contain 114 numbered theorem-like statements in their full TeX
input closures: 2 in the calculator paper, 13 in the foundations, 24 in the
ordering paper, 21 in equality/one-variable comparison, 18 in multivariate
fragments, 21 in source expressivity, and 15 in descent/modular counts.
Definitions, algorithms and cited supplier theorems add obligations beyond that
statement count. The root register remains authoritative for the whole collection.

| Paper | Reuse and formalization requirements |
|---|---|
| 04 — pure R1 calculator | The checked source constructs actual single-relation semantics, finite induced diagrams, endpoint characterization and sharp additive-tree norm bound. Preserve its separation from simultaneous order two. Legacy calculator modules are not importable by modern Lean modules. The selected modern norm closure is included with provenance; the calculator itself stays frozen. Python-to-Lean refinement is not silently added to its current coverage. |
| 05 — foundations | `foundations.tex` is part of the paper. The source norm matches `R1Calculator.treeWeight` exactly. After finite balls/control, construct the actual norm-controlled collapse on normal notations and pay maximum-predecessor, evaluator, count and original-source translation results. |
| 06 — termination ordering | Needs literal typed Gödel-T syntax and binding, finite type closure, coherent constructor families, the monotone fixed-point comparator, contextual/substitution stability and rule orientation. Ranked RPO and the ID1/Bachmann–Howard height supplier require their own checked chain, not an ordinal-bound hypothesis. |
| 07 — equality and one variable | Depends on the exact fixed collapse from 05. Normal forms, root/peak separation, exact suffix kernels and the simultaneous separation/termination certificate must be supplied, including effective source translation. |
| 08 — multivariate fragments | Includes the genuine Snyatkov first-order theory supplier and the actual source interfaces. Its finite/polynomial/common-head fragments must not import arithmetic decidability as an unproved field. |
| 09 — source expressivity | Both `source-realization.tex` and `hardness.tex` are part of the paper. Requires literal source assignments, guard-preserving arithmetic gadgets/Boolean compiler, whole-source construction and the polynomial-semiring undecidability supplier. |
| 10 — descents and counts | Depends on the actual 05 descent. Then requires growing-budget transfer, exact retained-source parameters, restricted-partition coefficients, Cartier/rational-state semantics and the exact tuple-period proof. Full-state periods must not be promoted to scalar-bit impossibility. |

## Reuse assessment

The calculator already adapted the relevant finite formula/diagram constructions
from the 3.1.3 project. Its `Norm.lean` defines exactly the additive norm required
here, and its standard normal notation package gives decidable normality and
well-founded actual ordinal comparison. Those are the first chosen dependencies.

The older 3.1.3 development also contains many Wilken/Carlson modules. Their
aggregate status does not certify a new supplier: some are explicitly marked
uncompiled candidates and some expose conditional interfaces. The current
norm/control candidates need none of those additional modules. Any later reuse
will be selected by exact statement, import closure, source provenance and an
axiom audit, with necessary local source included publicly. No private module
path is an accepted dependency.

In particular its `Wilken/FiniteCollapse.lean` implements a hull/minimum
construction with an upper-cardinal fallback (a different Wilken Definition
2.1), not the norm-controlled natural-valued collapse in these papers.
It is not reused merely because it has a similar name.

After a later explicit restart only: prioritize the actual-ordinal representation supplier and the existing
natural-sum algorithm/denotation proof candidates, which block promotion of
normal-notation components to the full source statements. Preserve the accepted
proof/semantic SHA pins; put extensions in separate files. Finite-tail/saturation
and source-kernel structural candidates remain pending. Native slot reservations cover running invocations only;
source repairs do not hold the shared compiler. No uncompiled candidate is an
accepted paper theorem.
