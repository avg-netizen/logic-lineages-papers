module
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteProbeProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAbsolute

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence

theorem formulaExact : CurrentAbsoluteTargets.FormulaExact := by
  intro p f hf Γ τ hg d ρ v
  let c := anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩)
  let k := AbsoluteObserver.factor τ
  have hk : 0 < k := by simp [k, AbsoluteObserver.factor]
  constructor
  · intro h
    obtain ⟨x,y,heq,hlin⟩ := h
    obtain ⟨n,_,hn⟩ := scalar_total p f ρ d.term
    have ha := (probeIdentity p f hf Γ τ hg d ρ n x y hn).mp heq
    change k*n+(x+1) = k*c+(y+1) at ha
    change k*v+(x+1) = k*c+(y+1) at hlin
    have ev : v = n := Nat.eq_of_mul_eq_mul_left hk (by omega)
    rwa [ev]
  · intro hv
    have hlin : k*v+(k*c+1) = k*c+(k*v+1) := by omega
    exact ⟨k*c,k*v,(probeIdentity p f hf Γ τ hg d ρ v _ _ hv).mpr hlin,hlin⟩

theorem full : CurrentAbsoluteTargets.Full := ⟨anchorExact, anchorEffective, probeIdentity, formulaExact⟩

end LogicLineages.ControlSensitivityCurrent.CurrentAbsolute
