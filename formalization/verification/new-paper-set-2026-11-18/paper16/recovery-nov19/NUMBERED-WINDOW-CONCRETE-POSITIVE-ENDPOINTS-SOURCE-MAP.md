# Original positive endpoints and its actual endpoint-carrier refinement

Target freeze only; neither packet is inferred accepted. Paper 16,
`16-persistent-marking-termination-ordering/sections/ordinals.tex` lines 10–29
fix the arithmetic carrier and retain finite contexts/fresh extension; lines 53–75
distinguish function-side auxiliary reduction, quotient congruence and a **positive**
class path with original numerical witnesses. Lines 77–96 use typedness in
the actual positive arithmetic accessibility operator. This packet supplies
supporting interfaces for that typed carrier, not the numbered accessibility
proof or the rest of that constructor induction.

## Core: the original supplied witness

* `NumberedWindowConcreteCheckers.step` is the original concrete raw root
  followed by `RawContextAlgorithm.windowStep`. That guard is literally
  `raw root q w r && admitted s ctx ty q && admitted s ctx ty r`.
  `ExactConcretePositiveHopReport` unfolds the actual successful
  `PositivePathAlgorithm.advance` on the given code: its same `hopView`
  provides `(target,q,w,r)`, the actual callback matters, and **both** original
  least checks must succeed. The raw root, raw witness, raw inputs, context,
  and requested type are retained; no correspondence to another checker
  or assumption on the shape of the raw term is needed.
* `ExactConcretePositiveBoundaryHops` starts from the actual original
  `positive` inside the address checker. It reads the caller's **same**
  `unpack witness` result. The actual nonempty supplied list is both
  `first :: rest` and `beforeLast ++ [last]`. Its first result comes from
  original `advance` on `some source`. Its last input comes from original
  `foldl advance (some source)` on exactly `beforeLast`, and original last
  advance reaches `some target`. The two literal hop reports expose all raw
  coordinates. The singleton has the same first and last; no minimal length
  two, fabricated trace, symmetric edge, or new encoded certificate.
  This follows from append/cons decomposition and preservation of `none`
  by original `advance` and its fold, not from any hypothesized path theorem.
* `ExactConcretePositiveRawEndpoints`: at the **first** hop the admitted
  raw predecessor has original least `some source`, and at the **last**
  hop the admitted raw successor has original least `some target`. Use
  the actual original `exact_RawLeastClosureWithVertices` (#683) twice,
  discharging its same-ordered-pool edge premise by the actual
  `exact_OriginalGuardedEdgeVertices` (#687). These prove raw admission
  and own least at both original visible results. No seed admission hypothesis
  is imposed on the caller, because the actual raw step supplies it.
* `ExactConcretePositiveScalarEndpoints`: original outer `addressRS`
  must have both successful exact `addressView` results, equal original context
  lists and equal result-type numbers, and the same positive walk. Feed the
  raw result above to the actual `canonical` on each actual parsed address,
  so `scalar s x = true` and `scalar s y = true` are established on the
  caller's original packed numbers. Invalid addresses/codes reject by the
  original checker. Nothing here assumes an arbitrary application result
  already supplies an admitted seed. The named fixed-S,K application-scalar
  target/resource stop is unrelated and remains unpaid.

All four contracts hold for arbitrary original `Entries`, `Settings`,
context/request where appropriate, and raw code inputs, conditional only on
the indicated actual concrete success. Target dependency closure is Init-only;
preflight/final Core stay at original 1536 heap/512 RSS/768 min-free/90 CPU/
180 wall/one thread. The old accepted suppliers and algorithms are immutable.

## Mathlib: one literal Program replacement, numeric only

`withEndpointCarriers i r` is physically
`bothOne r (bothOne (atSource i) (atTarget i))`. It uses the original
normalizer and the same typed scalar/positive programs. The tape order is
still `[x,w,y]`: old `r` sees all three unchanged, `i` sees the original
source and target, and the old witness is never repacked or replaced.
`ExactNumericEndpointCarrierBranches` specifies the exact normalized
all-input branch output even for arbitrary non-bit Programs. The intended
proof uses the calibrated literal projections and `bothEvaluation`.

`ExactOriginalPositiveEndpointRefinement` requires only the actual old
all-code scalar and positive graph calibrations, and derives rather than
assumes both endpoint carrier tests using the Core source result above.
If the original positive bit is false, the new normalized program rejects
regardless of any scalar result. `ExactOriginalPositiveEndpointPresentationEvaluation`
replaces exactly the positive Program in the original `Evaluates`, retaining
the actual `i,j,d`. Original Mathlib heap2048/RSS1536/min-free2048/CPU90/
wall180/one thread; Core results imported as actual Lean sources under the
Mathlib gate, never mixed receipts or accepted by numerical substitution.

No open object proof, body transfer, chosen `r''`, new tuple, retagged
accessibility, application output carrier, lexically canonical fresh variable
or neutral `C` is paid by these numerical claims. A later actual chosen
positive/body integration must prove the new program's own same-tape open
graph consequences and build its own `Interprets`/`Rules` rather than
transport old proofs by numerical equality.
