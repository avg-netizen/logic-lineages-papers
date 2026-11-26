module
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsTargets
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)

theorem positiveNoCollapse : CurrentAffineHeadsTargets.PositiveNoCollapse := by
  intro Γ i e hi hg
  revert hi
  induction hg with
  | one i => intro _; exact ⟨rfl,fun _ _ => rfl⟩
  | omega i hi => intro _; exact ⟨rfl,fun _ _ => rfl⟩
  | var x j => intro _; exact ⟨rfl,fun _ _ => rfl⟩
  | add ha hb iha ihb =>
    intro hi
    obtain ⟨ca,ha'⟩ := iha hi
    obtain ⟨cb,hb'⟩ := ihb hi
    constructor
    · simp only [collapseFree,ca,cb,Bool.and_self]
    · intro f ν
      simp only [denoteWith,denote,ha' f ν,hb' f ν]
  | emul hi ha hb iha ihb =>
    intro _
    obtain ⟨ca,ha'⟩ := iha (by omega)
    obtain ⟨cb,hb'⟩ := ihb hi
    constructor
    · simp only [collapseFree,ca,cb,Bool.and_self]
    · intro f ν
      simp only [denoteWith,denote,ha' f ν,hb' f ν]
  | collapse ha hb ihf ihg =>
    intro hi
    omega

theorem sameCommonUnits : CurrentAffineHeadsTargets.SameCommonUnits := by
  intro Γ ρ
  funext z
  rcases z with ⟨σ,x,j⟩
  cases σ with
  | ground =>
    change OriginalDomain.closedValue (UnitObservation.positive (ρ x)) = ((ρ x+1 : Nat) : Ordinal)
    exact UnitObservation.Proof.positiveValue (ρ x)
  | arrow a b => rfl

end LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads
