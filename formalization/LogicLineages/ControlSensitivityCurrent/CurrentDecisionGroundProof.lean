module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerStatementChecks
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteAnchorProof
public import LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence ExistentialPlan
open RawSourceDAG.InputCompiler (encodeInput)

theorem arithmeticReduction : CurrentDecisionTargets.ArithmeticReduction := by
  intro p f hf n q
  have hc := CurrentCompiler.StatementChecks.fixed_complete_compiler
  have ho := (hc.2.1.1 n q).2
  have h := hc.2.2.2.2.1 f hf p n q
  exact ⟨ho,h.1,h.2⟩

private theorem groundCompare (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool)
    {Γ : List Ty} (a b : OriginalTerm Γ .ground) (ρ : Variable Γ .ground → Nat)
    (av bv : OrdinalVector Γ 0)
    (ha : AdmissibleAssignment.assignment p a = some av)
    (hb : AdmissibleAssignment.assignment p b = some bv) :
    CurrentCounterBound.compareAt f strict av bv (fun c => inputs ρ c + 1) ↔
      if strict then PolicyCollision.rawScalar p f (inputs ρ) a < PolicyCollision.rawScalar p f (inputs ρ) b
      else PolicyCollision.rawScalar p f (inputs ρ) a ≤ PolicyCollision.rawScalar p f (inputs ρ) b := by
  obtain ⟨v,_,hs⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) a
  obtain ⟨w,_,ht⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) b
  have hv := PolicyOrderWrapper.raw_of_scalar p f (inputs ρ) a v hs
  have hw := PolicyOrderWrapper.raw_of_scalar p f (inputs ρ) b w ht
  obtain ⟨av',ha',va⟩ := hs
  obtain ⟨bv',hb',vb⟩ := ht
  rw [ha] at ha'
  rw [hb] at hb'
  cases Option.some.inj ha'
  cases Option.some.inj hb'
  unfold CurrentCounterBound.compareAt
  have hpos : ∀ j : Nat, CurrentCounterBound.coordinate f av (fun c => inputs ρ c + 1) (j+1) ≤
      CurrentCounterBound.coordinate f bv (fun c => inputs ρ c + 1) (j+1) := by
    intro j
    simp only [CurrentCounterBound.coordinate, ordinalVectorAt, dif_neg (show ¬ j+1 < 0+1 by omega)]
    exact le_rfl
  have ca : CurrentCounterBound.coordinate f av (fun c => inputs ρ c+1) 0 = (v : Ordinal) := va
  have cb : CurrentCounterBound.coordinate f bv (fun c => inputs ρ c+1) 0 = (w : Ordinal) := vb
  rw [and_iff_right hpos,ca,cb,hv,hw]
  cases strict <;> simp

theorem groundSpecialization : CurrentDecisionTargets.GroundSpecialization := by
  intro p f strict n a b
  let Γ := List.replicate n Ty.ground
  have hg : Ground p f strict a b ↔ ∀ ρ : Variable Γ .ground → Nat,
      if strict then PolicyCollision.rawScalar p f (inputs ρ) a.term < PolicyCollision.rawScalar p f (inputs ρ) b.term
      else PolicyCollision.rawScalar p f (inputs ρ) a.term ≤ PolicyCollision.rawScalar p f (inputs ρ) b.term := by
    cases strict <;> exact Iff.rfl
  rw [hg]
  constructor
  · rintro ⟨av,bv,ha,hb,h⟩ ρ
    exact (groundCompare p f strict a.term b.term ρ av bv ha hb).mp (h ρ)
  · intro h
    obtain ⟨av,ha,_,_⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ .ground a.term
    obtain ⟨bv,hb,_,_⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ .ground b.term
    exact ⟨av,bv,ha,hb,fun ρ => (groundCompare p f strict a.term b.term ρ av bv ha hb).mpr (h ρ)⟩

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
