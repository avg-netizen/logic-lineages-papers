module
public import LogicLineages.OrdinalComparison.SourcePolynomialRealizationTargets
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization.Proof

open OriginalDomain

theorem cnfRealization (p : NonnegativePolynomial) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega0 ^ Ordinal.omega0 ∧
      SignedPair.signedCNF a = embeddedCoefficients p := by
  classical
  let E : Nat ↪ Ordinal.{0} := ⟨fun n => (n : Ordinal), Nat.cast_injective⟩
  let f : Ordinal.{0} →₀ Ordinal.{0} :=
    Finsupp.embDomain E (p.mapRange (fun n : Nat => (n : Ordinal)) (by simp))
  have hfinite (n : Nat) : f (n : Ordinal) = (p n : Ordinal) :=
    Finsupp.embDomain_apply_self E _ n
  have hzero (e : Ordinal.{0}) (he : e ∉ Set.range E) : f e = 0 :=
    Finsupp.embDomain_notin_range E _ e he
  have hcoeff : ∀ e, f e < Ordinal.omega0 := by
    intro e
    by_cases he : e ∈ Set.range E
    · obtain ⟨n, rfl⟩ := he
      change f (n : Ordinal) < Ordinal.omega0
      rw [hfinite]
      exact Ordinal.natCast_lt_omega0 (p n)
    · rw [hzero e he]
      exact Ordinal.omega0_pos
  have hexponents : ∀ e ∈ f.support, e < Ordinal.omega0 := by
    intro e he
    by_cases hr : e ∈ Set.range E
    · obtain ⟨n, rfl⟩ := hr
      exact Ordinal.natCast_lt_omega0 n
    · exact False.elim ((Finsupp.mem_support_iff.mp he) (hzero e hr))
  refine ⟨Ordinal.CNF.eval Ordinal.omega0 f, Ordinal.CNF.eval_lt hcoeff hexponents, ?_⟩
  ext e
  rw [SignedPair.Proof.cnf_apply, Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0 hcoeff]
  by_cases he : e ∈ Set.range E
  · obtain ⟨n, rfl⟩ := he
    change (finiteValue (f (n : Ordinal)) : Int) = embeddedCoefficients p (n : Ordinal)
    rw [hfinite, SignedPair.Proof.finite_nat]
    unfold embeddedCoefficients
    rw [Finsupp.mapDomain_apply Nat.cast_injective (signedCoefficients p) n]
    rfl
  · rw [hzero e he, SignedPair.Proof.finite_zero]
    exact (Finsupp.mapDomain_notin_range (signedCoefficients p) e he).symm

end LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization.Proof
