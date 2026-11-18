module
public import LogicLineages.CartierObserverCurrent.F2DescentTargets
public import LogicLineages.CartierObserverCurrent.SplittingRootsProof
public import LogicLineages.CartierObserverCurrent.CanonicalExtensionProof
public import Mathlib.Algebra.Polynomial.Lifts
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.F2Descent
open SplittingRoots Polynomial

private theorem scalar_fixed (d : Nat) (a : ZMod 2) :
    frobenius (FieldAt d) 2 (algebraMap (ZMod 2) (FieldAt d) a) =
      algebraMap (ZMod 2) (FieldAt d) a := by
  apply (fixedFieldExactlyF2 d _).mpr
  exact ⟨a, rfl, fun b hb => (algebraMap (ZMod 2) (FieldAt d)).injective hb⟩

private theorem polynomial_image_fixed (d : Nat) (Q : Polynomial (ZMod 2)) :
    (Q.map (algebraMap (ZMod 2) (FieldAt d))).map (frobenius (FieldAt d) 2) =
      Q.map (algebraMap (ZMod 2) (FieldAt d)) := by
  ext n
  simp only [coeff_map]
  exact scalar_fixed d _

theorem polynomialDescent : Targets.PolynomialDescent := by
  intro d P
  constructor
  · intro h
    have hl : P ∈ Polynomial.lifts (algebraMap (ZMod 2) (FieldAt d)) := by
      apply (Polynomial.lifts_iff_coeff_lifts P).mpr
      intro n
      have hc := congrArg (fun Q : Polynomial (FieldAt d) => Q.coeff n) h
      simp only [coeff_map, frobenius_def] at hc
      obtain ⟨a, ha, _⟩ := (fixedFieldExactlyF2 d _).mp hc
      exact ⟨a, ha⟩
    obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts P).mp hl
    refine ⟨Q, ⟨hQ, ?_⟩, ?_⟩
    · rw [← hQ, degree_map_eq_of_injective (algebraMap (ZMod 2) (FieldAt d)).injective]
    · intro R hR
      exact Polynomial.map_injective _ (algebraMap (ZMod 2) (FieldAt d)).injective (hR.1.trans hQ.symm)
  · rintro ⟨Q, ⟨hQ, _⟩, _⟩
    rw [← hQ]
    exact polynomial_image_fixed d Q

private theorem rational_image_fixed (d : Nat) (g : RatFunc (ZMod 2)) :
    Naturality.rationalMap (frobenius (FieldAt d) 2)
      (Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) g) =
      Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) g := by
  conv_lhs => rw [← g.num_div_denom]
  rw [map_div₀, Naturality.extensionPolynomial, Naturality.extensionPolynomial,
    map_div₀, Naturality.extensionPolynomial, Naturality.extensionPolynomial,
    polynomial_image_fixed, polynomial_image_fixed]
  rw [← Naturality.extensionPolynomial (ZMod 2) (FieldAt d),
    ← Naturality.extensionPolynomial (ZMod 2) (FieldAt d), ← map_div₀, g.num_div_denom]

theorem rationalDescent : Targets.RationalDescent := by
  intro d f
  constructor
  · intro hf
    have hn : f.num.map (frobenius (FieldAt d) 2) = f.num := by
      rw [← CanonicalExtension.numeratorMap, hf]
    have hd : f.denom.map (frobenius (FieldAt d) 2) = f.denom := by
      rw [← CanonicalExtension.denominatorMap, hf]
    obtain ⟨P, ⟨hP, _⟩, _⟩ := (polynomialDescent d f.num).mp hn
    obtain ⟨Q, ⟨hQ, _⟩, _⟩ := (polynomialDescent d f.denom).mp hd
    have hQ0 : Q ≠ 0 := by
      intro h
      rw [h, Polynomial.map_zero] at hQ
      exact f.denom_ne_zero hQ.symm
    let g : RatFunc (ZMod 2) := algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) P /
      algebraMap (Polynomial (ZMod 2)) (RatFunc (ZMod 2)) Q
    have hg : Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d)) g = f := by
      dsimp [g]
      rw [map_div₀, Naturality.extensionPolynomial, Naturality.extensionPolynomial, hP, hQ]
      exact f.num_div_denom
    refine ⟨g, hg, ?_⟩
    intro r hr
    exact (Naturality.rationalMap (algebraMap (ZMod 2) (FieldAt d))).injective (hr.trans hg.symm)
  · rintro ⟨g, hg, _⟩
    rw [← hg]
    exact rational_image_fixed d g

#audit_namespace LogicLineages.CartierObserverCurrent.F2Descent
end LogicLineages.CartierObserverCurrent.F2Descent
