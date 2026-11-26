# Paper 17: independent printed correspondence, records 700 and 702–704

Read-only audit against owner head `762b1c9122ede8c5b752e0be277ff7657f30f099`. Compared printed `sections/entries.tex` and `sections/arithmetic.tex` with frozen targets, actual proof bodies, StatementChecks aliases, owner receipts and recursive evidence. No new native run; the owner records and inventory are unchanged.

| Owner record | Boundary independently established by source inspection | Frozen pins | Recursive source hashes |
|---|---|---:|---:|
| 700 | Printed threshold construction, on its effective tail | 6/6 | 290/290 |
| 702 | Abstract charge decrease for specified replacement relation | 2/2 | 3/3 |
| 703 | Five actual first-entry arithmetic clauses | 7/7 | 266/266 |
| 704 | LongField comparison plus a supplied-length short identity | 9/9 | 278/278 |

Recomputed every listed module source digest from checkout bytes after mapping the recorded native checkout prefix to this repo. Evidence JSON digests match the owner records: 700 `a792d60775f00e10b47dd4bd883110f603cdfa22be3e40b36b8bc84581facb33`; 702 `d72a81c34836c0dd4fb2c5c16be798eabb16e1aff0846a0a8f0e7c71a98c09a2`; 703 `fc4283d2ad4be1a7f5321daecfae3d183d2b96e3a303497acc1fa11d072e556b`; 704 `d3963a0317470320df144a07752909f1d211374c430255694c5d60e637fd3f21`. These are static identity checks. They do not revalidate native output digests, compiler or peak RSS.

## 700: threshold (entries.tex, prop:threshold)

No missing printed clause found. `FullThreshold` is about both selected controls, proper fixed intervals and an effective tail, not unconditional totality. The base proof constructs actual first entries and on-tail program membership with unique correct output. The three gap orders are genuine cases: in equal gaps raw order or the equal-input certificate applies; unequal gaps compute the actual auxiliary first hit and use the exact inverse-table row (or the reversed comparison). The effective guards account for the intermediate endpoints of both orientations and certificate dependencies. Program evidence is not an assumed comparison oracle: raw tails are primitive recursive, and the base and translated programs are partial recursive for computable control. The signed-translation proof enforces nonnegative translated inputs, then exact signed output comparison: unequal base outputs preserve order, while a collision uses precisely the output-offset comparison. Code calibration and offset tail effectiveness are separate proved clauses.

## 702: inner termination (arithmetic.tex, lem:inner-termination)

`FullInnerTermination` proves the abstract accounting inequality without a measure-decrease assumption. `Finsupp` does the syntactic combination and removal of zero coefficients. Every local disposition has the advertised bound: ended contributes zero, survivor one field, and a transfer at most two fields at strictly smaller rank (`2 * 3^a < 3^b`). An ordinary deletion lowers V; otherwise the integer zero-coefficient test excludes exactly one active count, and the proof finds a strict count-charge decrease by removal, transfer or merge. Both measures are separately nonincreasing.

The relation defining a step assumes the chosen class, the survivor rank and representative, and each prescribed update. There is no checked bridge from actual class guards, first-entry equalities and signed count transfers to those witnesses. Such a bridge should choose the smallest surviving input, classify actual identity/short/ended pieces, merge same-input survivors, transport higher-rank survivors and identify the normalized concrete row with the abstract update. All-ordinary/no-survivor cases also need an instantiation of the abstract dummy rank and label or a separate accounting clause. This is a concrete-application gap, not a failure of the abstract theorem.

## 703: count transfer (arithmetic.tex, count-core and lem:count-transfer)

The five actual semantic clauses, not just the names, were inspected:

1. Long-interval core identity: proper actual endpoints, both selected controls, explicit affordability tail. Actual prefix and full first entries support the doubled integer identity; the identity prefix is allowed.
2. Common-core zero class: supplied first-entry counts and a single shared core value, integer coefficients with `2b + Σa = 0`, exact signed prefix-plus-constant replacement. Repeated/shared inputs are not replaced by independent variables.
3. Equal-input merge: coincident actual entry norms imply equal counts by strict control iteration.
4. Distinct-input collision: on the gap tail and in strict input order, equality of actual entry norms forces a strictly smaller ordinal gap at the larger input.
5. Rank transfer: on the actual inverse-table tail with the smaller interval represented as `(ν+δ,ν)`, collision forces the equality row, an actual partner entry of norm equal to the larger input, and the correct additive count identity. It is applied after the strict gap clause; an arbitrary proper interval needs the ordinal representation bridge `ν + (λ - ν) = λ`.

These support concrete zero-class replacement; they do not implement full class selection, merged/short-piece bookkeeping, guard transport, or the application to 702.

## 704: field comparison (arithmetic.tex, lem:field-comparison)

The checked restricted result is useful. Field values are actual first-entry orbits with uniqueness. The supplied-length short identity holds on its explicit tail. On two LongFields, the same-input form gives fixed comparison; the distinct `x < y` form yields a fixed answer or an exact inverse-table row with nonlinear parameter evaluated only at the smaller coordinate. Properness of its parameter field is proved; it need not be long. Actual peeling/cocycle and certificate cases preserve the relevant comparison and order.

The printed statement covers **every** ordinary field and requires an **effective** finite Boolean form. Current correctness is restricted to LongField inputs, does not connect short normalization to the branch routines, and exposes existential tails rather than a uniformly computable tail interface. The form constructors are executable Lean definitions, but this is not a raw-code effectiveness/calibration theorem. A reversed-order branch can be assembled by swapping arguments and reversing comparison, but does not remove the short-field restriction.

Concrete source check, **not** native evidence or a counterexample to the paper: for the short interval `(ω,0)`, the short identity gives `E(x)=f(x)` on its tail. Nevertheless `sameForm (.iterate 1) (.entry 0 ω 0)` returns 0 (less), not 1 (equal). Likewise the existing distinct routine returns constant less for `f²(x)` against `E(y)`; for sufficiently large `x` and `y=x+1<f(x)`, strict monotonicity gives the opposite result. The existing routines must not be exported unchanged to all proper fields.

Repair in stages: exact effective short/long classification, outer-iterate-preserving semantics and its explicit normalization tail; then raw-code comparison/tail calibration and full order-branch assembly. Do not count a preprocessing supplier alone as a numbered theorem.
