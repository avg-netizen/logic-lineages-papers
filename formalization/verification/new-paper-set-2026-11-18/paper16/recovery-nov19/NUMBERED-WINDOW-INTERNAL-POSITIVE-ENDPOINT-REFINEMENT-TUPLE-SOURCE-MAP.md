# Reinstall the actual endpoint-refined sparse positive tuple

Target freeze only. Paper 16 `ordinals.tex` lines 10–29 retain all numerical
contexts in the same original fixed finite universe, lines 65–96 keep typedness
and the original quotient positive-path relation in the actual arithmetic
accessibility operator, and lines 100–128 use typed computability plus fresh
argument probes in that presentation. These are **supporting** fresh
installation contracts, not those constructor proofs or the numbered theorem.

* **New presentation** at `R = withEndpointCarriers i r`. #692 pays the exact
  all-raw `Evaluates (checks xs s) i j R d` using the original numerical old
  checker, original witness slot and actual scalar program `i`; only `r`
  is replaced. Apply original `exact_InterpretsEvaluatingPrograms` to these
  new evaluations and the existing five original accessibility rule suppliers
  to `S = data i j R d`. No transported old `Interprets` or `Rules`.
* **Same `v` original tuple**, explicit unchanged `ValidWindow s W`. The actual
  original `TupleAt` data contains calibrated inputs, uniqueness, input
  guards, numerical chosenA/chosenH graphs, actual per-outer-c typed totality,
  a body-independent literal parsed probe contract, and actual per-c
  given-fresh alignment/carriers. Keep the same physical `v` and fixed `W`:
  its chosenA/H and applicationGuard have literally the same ASTs, so reuse
  only old **body-free** calibration/uniqueness/shape laws that have the same
  type. In particular `v.scalarProg` is the same prior selected Inputs field;
  no AST equality to the selected wrapper `i` is claimed. For input guards,
  the scalar formula is literally unchanged when only the positive field
  changes, and `InputGuards` quantifies an arbitrary body. Reinstantiate its
  rule; do not move a derivation between old and new bodies. Use the same
  original window child-closure proof and actual `exact_SameParsedTypedProbeTotal`
  again at new `S,c`, then actual `exact_GivenFreshAlignmentAndCarriers` on
  that new totality and guards. This follows the exact #660 same-input
  reinstall template; #675's physical p-star/h-star refinement is deliberately
  **not** applied.
* **Concrete single choice** using #676 `exact_ConcreteInstalledTuple`. Keep
  the same witnesses `i,j,cv,tv,d,p₀,raw,least,v`, the whole old
  `InstalledTupleAt`, and make a new `TupleAt` on
  `withEndpointCarriers i (addressPositive cv tv raw least)`. The old tuple
  already states the literal v.applicationGuard = guard i p₀ and the exact
  context/type/raw/least/positive callbacks. Since v is the same, actual
  guarded p and chosen h are not replaced or silently equated with p-star
  or h-star. Old `InstalledReportAt` stays evidence for the old body, and
  is not part of the new tuple. #693 and #694 supply independent object
  carrier/positive transitivity contracts but are not body transport or
  prerequisites for rebuilding this `TupleAt`.

No new scalar-admission assumption, uncalibrated callback identification,
fixed-`S,K` mixed program bridge, arbitrary application result carrier,
lexical-fresh canonicality, neutral `C`, or numbered accessibility.
Serialized original Mathlib caps only: 2048 heap/1536 RSS/2048 min-free,
90 CPU/180 wall/one thread. All prior checked sources remain immutable.
