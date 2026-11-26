# Paper 17: the concrete zero-class replacement and its charge (source review only)

**Unproved join.** This review compares the actual printed source and the live Lean
suppliers, including owner records 702/703. No new target, proof, checker run, native
gate, or acceptance is recorded here. This is a separate step from the low-strip
closed evaluator and the high-tail field comparators.

## Printed source and checked interfaces

- `17-permitted-control-canonical-comparison/sections/arithmetic.tex:95–122`:
  annotate an entire active nonshort count by its full leading value
  `C=f(E_prefix(x))`, actual prefix and signed offset
  `κ=1−ceil(N(μ)/2)`. This does **not** create an ordinary value occurrence or
  an additional active count. With ordinary coefficient sum `b` and signed
  count coefficients `a_i`, the exact zero test is `2*b+Σa_i=0`.
- `lem:count-transfer` (124–162, especially 130–161): remove the whole zero
  class, replace it by actual prefixes and offsets, discharge identity/short
  prefixes, merge at equal input, then transfer strictly higher surviving
  prefixes to a fixed least surviving input. Both terms of an actual transfer
  are read at that smaller input; all affected domain and norm guards apply.
- `lem:inner-termination` (166–195; label at 178): use `M=Σ3^rank` over
  active syntactic count keys and `V` equal to the number of ordinary nonlinear
  syntactic keys, after identical-field combination and zero deletion. Neither
  summand increases, and **the sum strictly decreases**. This gives a
  natural-valued well-founded measure for the zero-class loop; a separate
  `Lex` theorem is not required. Selection of the largest guarded class and
  the loop exit/nonzero branch are later call-site obligations (197–206).

All Lean paths below are relative to
`formalization/LogicLineages/PermittedControl/`. Record **703**
(`703-count-transfer.json`) checks `CountTransferTargets.FullCountTransfer`
via `CountTransferProof.lean` and `CountTransferStatementChecks.lean`.
`CountCore` pays the actual doubled formula and FirstEntry witnesses for the
original interval and its literal prefix with target `μ+ω²`.
`ZeroClassExact` is the finite signed identity given the common full value.
`EqualInputMerge` equates the two actual counts once their actual entry norms
coincide at the same input. `DistinctInputGap` proves the prefix at the
**larger** input has the smaller gap. `RankTransfer` supplies the actual
FirstEntry of `H=(λ_Q, μ_Q+δ_P)` at the smaller input `x`, with
`E_H(x)=y` and `τ_Q(x)=τ_H(x)+τ_P(y)`. The last two results have real
gap/inverse-table tail hypotheses at both coordinates; `RankTransfer`
does not expose the inverse comparison sign as an extra output. If an
implementation splits on that sign, use the actual inverse-table row semantics
from `InverseTableDefinitions.lean` and the checked table suppliers, not a
new premise that the sign is equality. These are semantic ingredients, not a
constructor for a whole row.

Record **702** (`702-inner-termination.json`) checks
`InnerTerminationStatementChecks.fixed_fullInnerTermination`, from
`InnerTerminationProof.fullInnerTermination`.
`InnerTerminationTargets.Row O ι r` has a signed constant, a value
`Finsupp`, and count coefficients keyed by `ι × Fin r`. Its
`ZeroClassReplacement` (79–87) is a relation on two such rows: it
requires actual nonempty selected support subsets, the integer zero test,
one `x0` and representative `q`, and an admissible disposition for each
selected count; it fixes both filtered supports, their replacements and the
signed constant. It has no row semantics and does not establish that the
selected dispositions came from actual equal cores or that `x0` was found
from the concrete syntax. `FullInnerTermination` (91–95) gives both
nonincreases and the strict sum for **any pair already in that relation**.
Neither record proves the proposed join.

## Smallest useful next theorem

On a finite syntactic signed row and a selected nonempty branch class, take the
actual control, canonical endpoint/field codes, fixed rank assignment after
identifying equal raw coordinates, the integer zero coefficient test, and the
source domain/common-core/required local affordability guards. Construct
**one fixed symbolic row** `R′` from the input syntax, designated class and
branch data **before quantifying over numerical assignments**. Verify:

1. Erasure of the two actual rows is exactly an instance of
   `InnerTerminationTargets.ZeroClassReplacement`. Count keys can be literal
   `(λCode, μCode, rank)`; ordinary keys can use the actual nonlinear
   `FieldComparisonTargets.ValueField` encoding through
   `LongFieldEffectiveTailTargets.{LongFieldCode,longFieldCode}`, pairing
   with the rank as needed. Do not charge `.iterate 0` or other affine
   contributions as ordinary nonlinear fields. Preserve the original affine
   part; `Row` does not represent it.
2. On **every** valuation of the fixed ranks satisfying the retained guards,
   both rows are defined on the claimed domain and their actual signed row
   values agree. Retain original domain/definedness guards separately even
   when a syntactic field disappears; otherwise cancellation could extend the
   source domain, for example inside a negated atom. Do not assume the desired
   value equality as a property of input dispositions, and do not use
   `∀ valuation, ∃ R′` in place of the fixed symbolic result.
3. Apply 702 directly to those erased rows. No change to the charge theorem
   and no additional lexicographic result are needed. Selecting a maximal
   class, effectivity of the full loop, and comparison domination are outside
   this local join.

For the construction, enumerate exactly the selected count support to apply
703's `ZeroClassExact`. Actual ordinary and annotated full values share the
same value on the branch, and injectivity of the selected `f` identifies their
prefix entry norms where needed. Remove identities and short prefixes first
(`EntryTableProof.identityEntry`; actual short count from the checked short
entry suppliers, e.g. `FieldComparisonProof.shortEntryIterate` on its stated
tail). Pick the least **surviving** rank and a deterministic representative
`Q′` there, using a fixed key order for ties. Merge remaining prefixes at
that rank by `EqualInputMerge`; for a higher prefix use
`δ=λ_P−μ_P` with the actual ordinal gap orientation/reconstruction,
`DistinctInputGap`, and `RankTransfer` on the required domains.
`ThresholdNoteCodeProof.ordinal_add_note_code` / `.ordinal_sub_note_code`
calibrate the actual code operations; `ThresholdTailBridgeProof` supplies
`normal_encoded_gap_tail` and `inverseTableTailCode_correct`. A contradictory
case must prove the branch unsatisfiable, not replace a valid row.

For a selected coefficient `a`, use the exact 702 dispositions:
`.ended (κ+k_prefix)` (identity has `k_prefix=0`), `.survives κ`,
or `.transferred (some H) κ`. The last produces
`+a*τ_Q(x0)−a*τ_H(x0)`; cast the actual count equality into integers
before subtraction. A known short `H` can instead produce
`.transferred none (κ−k_H)` when its own domain/count is paid. If it is
emitted first as a short count, short normalization remains a separate
nonincreasing step. If no prefix survives (including a pure ordinary class),
the representative is unused: pick a fixed dummy interval key and derive an
available rank from a selected occurrence; for the real syntax an active
class cannot exist with no coordinate. Keep `Q′` as the fixed syntactic
representative even if its final coefficient cancels. Combine only
**identical syntactic keys**, including coinciding keys outside the class;
semantic equality on the guard is used only in the explicitly justified
class rewrite. These high-tail laws must not be silently applied on
below-threshold strips.
