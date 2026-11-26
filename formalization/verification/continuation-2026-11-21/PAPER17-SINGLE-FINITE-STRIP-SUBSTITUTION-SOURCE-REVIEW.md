# Paper 17: one finite-strip specialization (source review only)

**Existing checked suppliers; strip adapter unproved.** This note adds no Lean
target, proof, compiler run, or acceptance. In
`17-permitted-control-canonical-comparison/sections/arithmetic.tex:249–254`,
fix one raw coordinate to a permitted value below the common cutoff. Use that
same value everywhere, with the true definedness flags; all other coordinates
stay unbounded. This is an entire infinite strip, not a finite cube. The graph
equations and domain restrictions stay outside the possibly negated output
test (lines 34–43). Fixed argument shifts are affine aliases, and the field
arguments remain the actual raw coordinates (45–55). The finite-strip step
precedes the all-large greatest-coordinate projection (256–265).

## Literal checked suppliers

Under `formalization/LogicLineages/OrdinalComparison/LayeredComparison/SnyatkovCompletion/`,
`BoundedRowsDefinitions.lean` defines the actual `BoundedRows.substitute i n`
on `NormalForm.Formula` and `BoundedRows.Code.formula i n code` on the raw
radix-six formula code. For every occurrence with name `i`, the row fold adds
the fixed value times its signed integer weight to the constant. It keeps all
other occurrences in their original order, including zero weights. Atom kind,
divisibility modulus, and Boolean tree (including negation) are unchanged.
On the actual plain-variable input every removed item evaluates to `n`;
the old H/Phi value branches of the general compiler are not used there.

- `BoundedRowsSemanticStatementChecks.{actual_row_substitution,exact_residual_occurrences}`
  give the literal signed value/update equality and exact residual occurrence list.
- `BoundedRowsSemanticStatementChecks.{actual_formula_substitution,exact_substitution_support}`
  give, for **every** slot valuation `ν`, the iff
  `(substitute i n p).eval ν ↔ p.eval (Function.update ν i n)`, and
  output name membership iff input membership and the name differs from `i`.
- `BoundedRowsCodeStatementChecks.{literal_code_calibration,actual_numeric_programs}`
  give the exact `Code.formula i n p.encode = (substitute i n p).encode`
  and `Primrec₂ (fun args : Nat × Nat => Code.formula args.1 args.2)`.
- `BoundedRowsSemanticStatementChecks.exact_original_domains` concerns the
  old Snyatkov summand cutoffs. It does not supply Paper 17 field/graph
  definedness. `BoundedRows.bounded` enumerates one token's value; it is
  not the correlated field evaluation needed for one fixed raw rank.

Archive `formalization/verification/cumulative-continuation-2026-11-04-second/bounded-rows/`:
read-only rehash verified all **4 frozen source pins and 161 closure-source
hashes** against the current files, with no differences. The archived final
receipt is `1793848563876614710-2`; no fresh native replay was performed.

Under `formalization/LogicLineages/PermittedControl/`, owner record **724**
uses `ClosedOrdinaryFieldTargets.lean` and
`ClosedOrdinaryFieldStatementChecks.lean`. Exact suppliers are
`StatementChecks.fixed_closedOrdinaryFieldEffective`,
`fixed_closedOrdinaryValueActual`, and `fixed_closedOrdinaryCountActual`
in that same namespace, backed by `fixed_closedProperEntryDomainExact` and
`fixed_closedProperEntryResultExact`. At the actual unshifted input `a`
they distinguish:

| Result | Exact meaning on actual typed operand codes |
|---|---|
| `none` | Invalid proper-field domain, including an unaffordable source input; no numerical default. |
| `some none` | Valid domain but no actual first entry; a genuine miss, not invalid input. |
| `some (some v)` | Actual field value (including the prescribed outer iterate) or actual first-hit event index. Zero is a valid hit. |

A raw table decoder must separately account for malformed syntax. In
particular, `closedOrdinaryValueField` treats every nonzero raw field tag
as an entry and ignores unused iterate payloads. The supplier's exact value
interpretation is for `longFieldCode F`, not a rejection theorem for every
malformed table or field tag. Whole strip computation uses the actual checked
`Computable f`-relative field reads; the pure syntax fold is primitive
recursive without any field evaluations.

## Shortest exact strip adapter

1. **Fix the raw rank, not a token value.** Retain the actual literal
   `PreparedProjection.LowerOperand` table encoding from
   `PreparedParameterProjectionTargets.lean`: positive name `j+1` refers
   to original slot `j`; names/codes of untouched slots do not change.
   With one given raw rank `x` and value `a`, enumerate the positively
   named slots actually needed by the live formula and its designated
   graph/domain component (or a separately specified all-required table).
   For every needed slot at rank `x`, use the same `a`: a raw coordinate
   yields `a`, an ordinary field uses its literal code and 724's value
   read, and a count uses its actual two endpoint codes and 724's count
   read. Duplicate field slots remain tied to that same actual argument and
   operand; never sample or existentially choose their values independently.
   Include name zero's update `(0,a)` only if zero denotes a separately
   designated raw coordinate whose rank literally is `x`.
2. **Fold the actual substitution.** From successful reads obtain a finite
   list of distinct touched **names** with their actual natural values.
   Fold `BoundedRows.substitute` (and `BoundedRows.Code.formula`) on the
   signed formula. For every abstract slot valuation, the new formula is
   equivalent to the original under those simultaneous updates, or the
   corresponding ordered fold of pairwise disjoint updates. Prove plain
   syntax survives and output name support is the original support minus
   touched names. This permits leaving unused/removed slots in the exact
   table bytes: they cannot affect the formula. Prove the fold's literal
   code calibration and primitive recursiveness by lifting the existing
   single-name suppliers; no new Presburger algorithm is needed.
3. **Recover actual one-rank source meaning.** Quantify over every common
   raw valuation `ρ` of all the other, still unbounded ranks. Compare to
   the original strip under `Function.update ρ x a`. The retained reads
   at ranks different from `x` depend only on their unchanged ranks; the
   fixed reads have the same genuine values for every such `ρ`. Preserve
   the output test's polarity and specialize the original outer graph and
   domain guards too. The actual pending endpoints are the all-valuation
   source iff, exact status/output and its raw computability, and support
   on the surviving raw ranks. Finite disjunction over permitted choices of
   `a`, coverage and branch policy across ranks, and induction over
   dimensions are later steps.

The current frozen `PreparedTableTied` quantifies over **all** table slots
and requires every slot defined and at a rank strictly below its selected
`zRank`. It is useful for a restricted low-strip case, not the general
pre-normalization finite strip: the fixed rank might itself be greatest and
have nonlinear calls. Reuse the table representation and plain signed grammar,
but use a distinct support-restricted invariant for the strip. It must admit
nonlinear operands on the rank being specialized and ignore obsolete slots
after actual named support has been removed. Do not change the frozen prepared
projection target or claim this restricted route closes the general branch.

## Failure, guards, and identity

A miss or invalid input is **not** an unconditional instruction to replace an
arbitrary Boolean formula by false. A required call may rule out the entire
flattened branch only after paying the actual implication “the original outer
graph/domain guard implies that this call has a value.” This implication is
independent of whether the output test is positive or negated. In contrast,
unused slots, inactive/local branches, and a Boolean occurrence under a
negation do not by themselves have this property. Keep invalid and valid
miss diagnostics distinguishable, and keep the outer guard separate from
the output's own connectives. If required-call evidence has not yet been
frozen, the defensible smallest packet returns the exact read statuses and
proves specialization on the hit path; do not silently treat a failed read
as a proof that the domain is empty.

For the thin proper-field packet keep identity entry/count normalization
separate. Bare coordinate `a` (or `.iterate 0`) is literal, and never
`2 * potential a`. `EntryTableStatementChecks.fixed_identityEntry` pays
actual first-hit index zero and actual norm `a` for an identity interval
with its original below-ε₀, zero-or-limit and source-norm hypotheses. An
outer iterate after identity is then literally `f^[k] a`. Preserve the
identity source guard when replacing the count by zero. Do not run an
identity interval through 724's strict proper-field guard and misread its
rejection as a genuine miss. Finite-head evaluation and an explicitly
chosen finite extension below its normal source domain are separate if
still present in the unflattened source.
