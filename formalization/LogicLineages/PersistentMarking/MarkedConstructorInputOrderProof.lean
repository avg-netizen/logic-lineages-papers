import LogicLineages.PersistentMarking.MarkedConstructorWeakOrderProof
import LogicLineages.PersistentMarking.MarkedConstructorFAbsOrderProof
import LogicLineages.PersistentMarking.MarkedConstructorValidityProof

namespace LogicLineages.PersistentMarking.MarkedConstructorInputOrderProof
open Spine DecisionPorts HereditaryDomainCode
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE weakenParameter)
open MarkedConstructorTargets (Replaces)

theorem replacements (E : Environment) (heads : List Head) (p q : Parameter)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hpq : InputLE E p q) (ts : List Expr)
    (h : Replaces E p.2.2.1 (p.1.arguments.zip p.2.2.2.1) ts) :
    Replaces E q.2.2.1 (q.1.arguments.zip q.2.2.2.1) ts := by
  rcases p with ⟨f,τ,Γ,bs,es⟩
  rcases q with ⟨g,υ,Δ,cs,fs⟩
  obtain ⟨hf,_,hΓ,hbase,_⟩ := hpq
  change f = g at hf
  change Γ = Δ at hΓ
  subst g
  subst Δ
  exact MarkedConstructorStatOrderProof.replaceOrder h
    (MarkedConstructorStatOrderProof.baseOrder E Γ f.arguments bs cs hp.2.2.1 hp.2.2.2.1 hq.2.2.2.1 hbase)

theorem inputMonotone : MarkedConstructorTargets.InputMonotone := by
  intro S E heads M p q hpfx hm hp hq hpq Δ hΔ he
  have heq : Extends q.2.2.1 Δ := hpq.2.2.1 ▸ he
  let a := weakenParameter E p Δ
  let b := weakenParameter E q Δ
  have ha := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hΔ he
  have hb := MarkedFamilyCoherenceFoundationProof.destinationValid E heads q Δ hq hΔ heq
  have hab := MarkedConstructorParameterProof.weakenMonotone E heads p q Δ hp hq hpq hΔ he
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro t _
    have hw := MarkedConstructorWeakOrderProof.weakOrder S E heads M M a b t ha hb hab.1 hab.2.1 hab.2.2.1
      (MarkedConstructorOwnerOrderProof.ownerInputOrder E heads M a b hm hb hab)
      (MarkedConstructorSelectOrderProof.tagsInputOrder E heads a b ha hb hab)
      (replacements E heads a b ha hb hab)
      (MarkedConstructorFAbsOrderProof.inputOrder E heads M a b t hpfx hm ha hb hab)
    exact ⟨hw,hw⟩
  · intro ds τ hpre xs hx
    exact MarkedConstructorValidityProof.tablesMonotone S E heads M p q Δ ds τ xs xs hpfx hm hp hq hpq hΔ he hpre hx hx
      (by
        intro i ρ a b hρ ha hb
        cases ha.symm.trans hb
        exact (HereditaryPartialOrderProof.partialOrder E ρ Δ hΔ).1 a (hx.2 i ρ a hρ ha))

theorem exact_InputMonotone : MarkedConstructorTargets.InputMonotone := inputMonotone
#print axioms exact_InputMonotone
end LogicLineages.PersistentMarking.MarkedConstructorInputOrderProof
