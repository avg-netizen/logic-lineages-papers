module
public import LogicLineages.OrdinalComparison.CartierOrbitDefinitions
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalDefinitions
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

/-- The actual coefficient extension of the F2 rational-function field. The
injection needed for the fraction-field lift is the library polynomial-map
injection followed by the canonical fraction-field injection. -/
noncomputable def actualBinaryRationalExtension (K : Type u) [Field K]
    [Algebra (ZMod 2) K] : RatFunc (ZMod 2) →+* RatFunc K :=
  IsFractionRing.lift (A := Polynomial (ZMod 2)) (K := RatFunc (ZMod 2))
    (g := (algebraMap (Polynomial K) (RatFunc K)).comp
      (Polynomial.mapRingHom (algebraMap (ZMod 2) K)))
    ((RatFunc.algebraMap_injective K).comp
      (Polynomial.map_injective _ (algebraMap (ZMod 2) K).injective))

end LogicLineages.OrdinalComparison
