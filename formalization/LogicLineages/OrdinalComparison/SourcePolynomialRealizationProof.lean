module
public import LogicLineages.OrdinalComparison.SourcePolynomialRealizationCNFProof
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization.Proof

theorem exactEmbedding : Targets.ExactEmbedding := by
  intro p
  have hcoef : ∀ n : Nat,embeddedCoefficients p (n:Ordinal)=(p n:Int) := by
    intro n
    unfold embeddedCoefficients
    rw [Finsupp.mapDomain_apply Nat.cast_injective]
    rfl
  refine ⟨hcoef,?_,?_⟩
  · intro e he
    apply Finsupp.mapDomain_notin_range
    rintro ⟨n,hn⟩
    have hlt := Ordinal.natCast_lt_omega0 n
    change (n:Ordinal)=e at hn
    rw [hn] at hlt
    exact (not_lt_of_ge he) hlt
  · ext n
    exact hcoef n

private theorem cnf_zero : SignedPair.signedCNF 0=0 := by
  simpa using SignedPair.Proof.cnf_nat 0

private theorem embedded_zero : embeddedCoefficients 0=0 := by
  simp [embeddedCoefficients,signedCoefficients]

theorem actualRealization : Targets.ActualRealization := by
  intro p
  by_cases hp : p=0
  · subst p
    refine ⟨0,Ordinal.opow_pos _ Ordinal.omega0_pos,?_,?_,by simp,by simp⟩
    · rw [cnf_zero,embedded_zero]
    · rw [cnf_zero]
      ext n
      simp [SourceFiniteExponentProjection.finitePart,signedCoefficients]
  · obtain ⟨a,ha,hcnf⟩ := cnfRealization p
    have hne : a≠0 := by
      intro hz
      rw [hz,cnf_zero] at hcnf
      apply hp
      ext n
      have hc := (exactEmbedding p).1 n
      rw [←hcnf] at hc
      simpa using hc.symm
    refine ⟨a,ha,hcnf,?_,?_,?_⟩
    · rw [hcnf]
      exact (exactEmbedding p).2.2
    · simp [hne,hp]
    · exact ⟨fun _ => hp,fun _ => lt_of_le_of_ne (show 0 ≤ a from zero_le) (Ne.symm hne)⟩
end LogicLineages.OrdinalComparison.Source.SourcePolynomialRealization.Proof
