# Paper 16: canonical positive coefficient model of the actual band order

The source order is the checked actual dependent sum `BandLex` below each
same fixed original native tower (Paper 16 ordinals.tex (B_T), (D), and the
native lower-witness construction). The model is exactly finite big-endian
lists of naturals with positive leading coefficient. Internal and trailing
zero coefficients are retained. The zero polynomial is absent on purpose:
dimension zero in the source means the first, one-coordinate positive band.

* `NativeTowerBandCoefficientModelProof` writes the leading band coordinate
  plus one, then each later coordinate literally in order. The model proof
  supplies exact length, true positivity, and a literal inverse using the
  leading coefficient minus one followed by repeated coordinate append.
  Both round trips are proved. Equal dimension corresponds exactly to
  ordinary `List.Lex Nat.lt`, with prefix ambiguity excluded by equal
  lengths. Arbitrary dimension uses length first, exactly as `BandLex`.
  This stage imports Lean core list lex, not Mathlib.
* `NativeTowerBandCoefficientRelIsoProof` makes the relation isomorphism
  using that explicit computable inverse, then composes with the already
  checked relation isomorphism onto the actual literal native image.
  The exact original native point for each coefficient list and the
  fixed physical t_(l+2) bound on every image term are both explicit.
  The well-order of the coefficient order is inherited from the same
  genuine relation. Only the existing lightweight relation/equiv imports
  are used.

This is a finite coefficient sequence presentation, not a Mathlib
ordinal interpretation or an ordinal arithmetic/rank computation. It
does not prove any equality to a named ordinal or to Bachmann–Howard.
