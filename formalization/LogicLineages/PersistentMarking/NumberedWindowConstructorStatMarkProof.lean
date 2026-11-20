import LogicLineages.PersistentMarking.NumberedWindowConstructorStatAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowMarkPathChecks
import LogicLineages.PersistentMarking.NumberedWindowSimulationQuotientProof

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorStatMarkProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowSimulationData
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticAllContextTargets NumberedWindowConstructorArgumentAddresses
open NumberedWindowConstructorStatAddressTargets

theorem carrierPath {S K C τ q r} (hk : DecisionSourceUniverse.Closed K)
    (hq : InWindow S K C τ q) (hMark : MarkDecrease q r) :
    ∃ hr : InWindow S K C τ r, RS S K C τ (classOf ⟨q, hq⟩) (classOf ⟨r, hr⟩) := by
  obtain ⟨trace, _, hPositive, hAdmitted⟩ :=
    NumberedWindowMarkPathChecks.exact_ArbitraryMarkDecreasePath S K C τ q r hk hq hMark
  obtain ⟨_, hr, hPath⟩ := NumberedWindowSimulationQuotientProof.positive
    S K C τ q r trace hAdmitted hPositive
  exact ⟨hr, hPath⟩

theorem slotCode {S K Γ q code} (h : slot S K Γ q = some code) :
    ∃ i, leastCode S K Γ q.type q = some i ∧ encodeAddress ⟨Γ, q.type, i⟩ = code :=
  Option.map_eq_some_iff.mp h

theorem addresses : MarkDecreasePositiveAddresses := by
  intro S K Γ q r source target hk hq hMark hSource hTarget
  obtain ⟨hr, hPath⟩ := carrierPath hk hq hMark
  obtain ⟨i, hi, hSourceCode⟩ := slotCode hSource
  obtain ⟨j, hj, hTargetCode⟩ := slotCode hTarget
  have hType := NumberedWindowApplicationDomainProof.annotation hr.1
  rw [hType] at hj hTargetCode
  exact ⟨Γ, q.type, i, j, classOf ⟨q, hq⟩, classOf ⟨r, hr⟩, hSourceCode, hTargetCode,
    ⟨⟨q, hq⟩, rfl, hi⟩, ⟨⟨r, hr⟩, rfl, hj⟩, hPath⟩

end LogicLineages.PersistentMarking.NumberedWindowConstructorStatMarkProof
