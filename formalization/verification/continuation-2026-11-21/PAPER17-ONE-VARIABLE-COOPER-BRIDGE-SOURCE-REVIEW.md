# Paper 17: formula-valued one-variable Cooper projection (source review only)

**Existing checked kernel; Paper 17 adapter unproved.** This review adds no
Lean source, native gate, or acceptance. The relevant printed contract is
`17-permitted-control-canonical-comparison/sections/arithmetic.tex:256–269`:
eliminate the greatest **natural** coordinate `z` on an already normalized
all-large/order branch, return a Boolean formula of linear inequalities and
congruences, and prove equivalence for **every** assignment to parameters
before substituting the actual correlated lower-field values. The fields'
original arguments may not change. The retained graph equations, natural
affine outputs, and shared-node conventions are in lines 3–8 and 34–55;
lines 297–302 exclude unrestricted same-forward-language nonlinear QE.

## Exact existing Lean suppliers

Under `formalization/LogicLineages/OrdinalComparison/LayeredComparison/SnyatkovCompletion/`:

| Actual declaration | Available guarantee |
|---|---|
| `LinearRowsDefinitions.lean`, `LinearRows.eliminate` | A concrete `Nat → NormalForm.Formula → NormalForm.Formula` transformer; no evaluator or valuation supplied to the program. |
| `LinearRowsSemanticStatementChecks.actual_linear_elimination` | Exact `LinearRowsTargets.ActualLinearElimination`: for every `i,p` with `isLinear i p = true` and **every** `ν : Nat → Nat`, `(eliminate i p).eval ν ↔ ∃ n : Nat, p.eval (Function.update ν i n)`. The linearity test checks even zero-weight occurrences. |
| `LinearRowsSupportStatementChecks.exact_output_support` | For any `i,p,j`, output variable-name membership iff `j ≠ i ∧ j ∈ p.variables`; do not confuse variable-name support with absence of nonlinear constructor tags. On pure-variable input the latter follows separately from the actual remainder/filter/scale/concatenate/substitute definitions, which never create a new summand. |
| `LinearRowsCodeStatementChecks.literal_code_calibration` | In particular `LinearRows.Code.eliminate i p.encode = (LinearRows.eliminate i p).encode`, for literal `NormalForm.Formula.encode`. |
| `LinearRowsCodeStatementChecks.actual_numeric_programs` | In particular `Primrec₂ LinearRows.Code.eliminate`; the range enumeration, syntax traversal and output constructor program really execute. |
| `LinearRowsSemanticStatementChecks.{actual_normalization,actual_unit_elimination,positive_coefficient_modulus,positive_unit_period}` | Exact natural normalization and elimination, with positive common multiples. |

Existing acceptance archive:
`formalization/verification/cumulative-continuation-2026-11-04-second/linear-rows/`
(`FROZEN-TARGETS.json`, `SOURCE-CLOSURE.json`, `ACCEPTANCE.json`; final
aggregate receipt `1793854211013438567-2`). All 3 archived frozen pins
and 226 archived closure-source hashes were compared with and match current
files. The archived aliases have standard-only axioms; this is a read-only
source rehash, not a fresh native replay or Paper 17 acceptance.

There is also a more economical typed alternative:
`ModelsAlgebra/Forests/CotreePresburgerNormalizeDefinitions.lean`'s
`CotreePresburgerNormalize.eliminate : QF (n+1) → QF n`, and
`CotreePresburgerNormalizeStatementChecks.lean`'s
`CotreePresburgerNormalize.StatementChecks.eliminationExact`:
for **arbitrary** `v : Fin n → Int`, `evalQF (eliminate p) v = true` iff
`∃ x : Nat, evalQF p (Fin.snoc v (x : Int)) = true`. Here
`CotreePresburgerUnit.QF n` has only signed affine inequality/divisibility
atoms with a Boolean tree, and `Fin.last n` is eliminated by the output type.
The pure executable typed transformer is distinct from its encoded
effectivity: the explicit already-audited `Primrec₂`/literal code pair
above is for **LinearRows**, not the Forest typed syntax. For one
code-calibrated Paper 17 pipeline, prefer `LinearRows` without proving a
new second eliminator. `NonlinearProjectionCompletion/TiedLinear{Definitions,Targets,CodeDefinitions,CodeTargets}.lean`
is an existing model of shared symbolic token lift/lower, but its concrete
H/Phi fields are not Paper 17 fields.

In the pinned Mathlib tree (`lake-manifest.json` pin
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`),
`Mathlib/ModelTheory/Arithmetic/Presburger/Basic.lean` lists QE as a TODO;
`Definability.lean` gives `presburger.definable_iff_isSemilinearSet` and the
unary eventual-periodicity theorem, not a formula-returning algorithm.
The repo's NFA word projection, satisfiability tests, and finite-support
theorems alone would also not supply the required result. The two explicit
repo transformers above do return the required kind of formula.

## Signed rows, moduli, and the finite witness range

A `NormalForm.Row` is an integer constant and a list of signed integer
weighted summands. `nonnegative R` means `0 ≤ R`; on integers use
`R−1 ≥ 0` for `R>0`, and encode equality by `R≥0 ∧ −R≥0`.
Disequality is its negation; no conversion to DNF is required. A positive
modulus `d` is encoded by `modulusMinusOne=d−1`. Thus `divisible 0`
in this encoding means **modulus one**, not mathematical divisibility by
zero. A congruence against a residue is `d ∣ (R−residue)`, its negation is
a permitted Boolean node. If source syntax allows a zero-modulus extension
defined by `0 ∣ R`, encode it as the appropriate equality separately;
never pass it through the positive-modulus compiler. Signed row
coefficients and representatives are not truncated to naturals.

The actual algorithm uses a positive common multiple `M` (product of
nonzero coefficient magnitudes, with zero given weight 1) and `y=M*z`,
guarded by `M ∣ y` and `y≥0`. For `a≠0`, the scale
`k=M/|a|>0` transforms `a*z+R` to `sign(a)*y+kR`. An inequality
requires no polarity reversal because the scaling is **positive**;
a divisibility atom `d ∣ a*z+R` becomes
`k*d ∣ sign(a)*y+kR`, not `d ∣ ...`. For `a=0` keep the original
remainder and the original modulus. The period `P>0` is the product of
the actual normalized positive moduli, including the guard `M ∣ y`.
Using products instead of LCMs is sound and already implemented.

The compiler enumerates literal affine cutpoints `b` in
`{0} ∪ {−R for y+R≥0} ∪ {R+1 for −y+R≥0}`, and every offset
`0 ≤ j < P`, substituting `b+j` in the **whole** guarded Boolean
formula. `CotreePresburgerUnit.Proof.{largest_cutoff,eval_same_cell,unitEliminationExact}`
give the proof: for a real witness `y≥0`, choose a largest *evaluated*
cutpoint `b≤y`, and replace `y` by `b+((y−b) mod P)` in the same cell.
The maximum is only a proof choice, not calculated from unavailable
parameters by the compiler. Both upper and lower truth patterns and signed
or negated divisibility are preserved; inspecting only lower rows would
need a conjunctive/DNF restriction not required by this kernel. Reverse
direction uses the enumerated candidate's actual nonnegative and
divisibility guards to recover a natural `z`. No negative-infinity case
is needed.

## Narrow Paper 17 adaptation and prior obligations

1. **Lift.** Freeze a translation of a prepared signed row/Boolean branch.
   Give selected raw `z` name **0**, shared by its raw occurrences, and
   each lower token a fixed positive name from a finite **syntactic** table.
   Tokens distinguish literal raw coordinates from actual lower fields:
   iterate/entry/count kind, normalized endpoint/iterate codes, and
   original argument coordinate. Repeated identical field keys may share
   one index; otherwise keep distinct indices. No key merges by sampling
   values, and no nonlinear field at `z` may be hidden as a parameter.
   Encode every operand as a plain `NormalForm.Summand.variable`, all
   integer coefficients and Boolean positions unchanged. Then
   `isLinear 0 = true` by syntax.
2. **Eliminate and lower.** Run the actual `LinearRows.Code.eliminate 0`,
   with its literal typed calibration. Prove output occurrences remain
   plain variables and names are from the original table, nonzero; use
   exact support plus the row/summand invariants. Lower each surviving
   index literally to the original coordinate or field token with the
   identical argument. The adapter's own total raw lift/lower code
   (including explicit behavior for bad codes) and code agreement remain
   to prove. The Forest typed route offers no-fresh-index by type but
   still needs its own raw coding/effectivity if selected.
3. **Meaning under one assignment.** First prove the compiled formula iff
   `∃ z : Nat` for **every** assignment of values to the retained tokens.
   Then evaluate each token once under the same original valuation of the
   lower raw ranks/shared circuit nodes, using actual defined values.
   The hypothetical assignments used to state the kernel theorem need not
   be realizable by the circuit; never existentially quantify the
   independent parameter names or assume their values independently
   realizable. Preserve source definedness guards and graph equations at
   their actual Boolean position, especially outside the negated output
   test. If using a totalized valuation for partial fields, prove the
   retained guards make it immaterial on source-defined valuations.
4. **Parity/domain preparation remains unpaid by this kernel.** For each
   current positive modulus `m`, build the literal shared raw residue table
   on `t mod 2m` (`arithmetic.tex:231–240`;
   `controls.tex:172–182,206–227`; `EntryStatementChecks.fixed_entryResidues`,
   `CountStatementChecks.fixed_completeCountResidues` and selected control
   orbit laws are supporting identities). `potential t = t/2` as Nat, so
   for `t=2m*q+r` the potential residue is `⌊r/2⌋` mod `m`. Keep the
   raw identity's **odd bit**: the identity field is `t`, not
   `2*potential t`. Test each signed combination using the single common
   residue per raw coordinate; do not independently choose residues for
   repeated terms. Apply only on the checked affordability/control tails;
   low strips require their own exact closed hit/miss/definedness supplier.
   Optional explicit halves need their own checked table or the exact
   natural graph `2h=f(q)` at the flattening point; annotations do not
   introduce new coordinates or extra half-values. Newly produced moduli
   are processed at the next smaller dimension, not by reentering the
   current cutoff loop.

The local next comparator should cover the two literal adapters, the
no-new-fields/no-`z` output grammar, and the displayed all-assignment
equivalence for a **prepared** normalized input branch. This alone does
not pay field-residue compilation, the concrete zero-class rewrite,
all-large guard normalization, below-cutoff evaluation, or the complete
closed-block induction.
