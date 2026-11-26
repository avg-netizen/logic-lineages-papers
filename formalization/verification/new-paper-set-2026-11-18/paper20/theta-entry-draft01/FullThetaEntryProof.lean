module
public import LogicLineages.CartierObserverCurrent.FullThetaEntryTargets
public import LogicLineages.OrdinalComparison.ThetaEntryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullThetaEntry
open LogicLineages.OrdinalComparison

theorem explicitFamily : Targets.ExplicitFamily := by
  intro v hv
  let Θ : Ordinal.{0} := Ordinal.omega0 ^ (Ordinal.omega0 + 1)
  let a : Ordinal.{0} := Θ + ((v - 4 : Nat) : Ordinal)
  have hf := actualFiniteTailClosureNorm Θ actualThetaFacts.1 (v - 4)
  have hn : actualOrdinalNorm a = v := by
    change actualOrdinalNorm (Θ + ((v - 4 : Nat) : Ordinal)) = v
    rw [hf.2, actualThetaFacts.2.2]
    omega
  have hl : actualLimitPart a = Θ := by
    obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp actualThetaFacts.2.1.isSuccPrelimit
    change actualLimitPart (Θ + ((v - 4 : Nat) : Ordinal)) = Θ
    unfold actualLimitPart
    rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 (v - 4)), add_zero]
  have h := actualThetaEntryWitness a hf.1 hl
  dsimp only at h
  rw [hn] at h
  exact ⟨hf.1, hn, hl, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1⟩

theorem completeEntry : Targets.CompleteEntry :=
  ⟨actualPhiResidueThree, actualThetaEntryWitness, explicitFamily⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullThetaEntry
end LogicLineages.CartierObserverCurrent.FullThetaEntry
