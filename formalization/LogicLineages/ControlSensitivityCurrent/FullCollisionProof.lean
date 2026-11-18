module
public import LogicLineages.ControlSensitivityCurrent.CollisionNumericProof
public import LogicLineages.ControlSensitivityCurrent.GenericScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullCollision
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PolicyCollision SourceCollisionCompletion
private theorem raw_total (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground) :
    0 < PolicyCollision.rawScalar p f ρ t ∧
    CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) t (PolicyCollision.rawScalar p f ρ t) := by
  obtain ⟨v,hv,n,hp,hn,hu⟩ := GenericScalar.actualSourceTotality p f Γ ρ t
  have he : PolicyCollision.rawScalar p f ρ t = n := by
    unfold PolicyCollision.rawScalar
    rw [hv]
    change OriginalDomain.finiteValue (ParametricSourceSuccessor.denoteWith f _ (v 0)) = n
    rw [hn]
    exact OriginalDomain.originalFiniteValueCalibration n
  rw [he]
  exact ⟨hp,(hu n).2 rfl⟩

private theorem eraser_scalar (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground) (x y : Nat)
    (ha : CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) a x)
    (hb : CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) b y) :
    CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) (eraser a b) (PolicyCollision.g f (3*x+y+2)) := by
  have hc := FullAddition.completeAddition.2.2.2 f hf
  have h := (CompositeEraser.finiteClosure p f hc.1 (fun n => (hc.2.1 n).le) Γ _ a b x y ha hb).1
  simpa only [PolicyCollision.g,Nat.add_assoc] using h

theorem completeCollision : Targets.CompleteCollision := by
  intro f hf p Γ ρ
  refine ⟨raw_total p f Γ ρ,?_⟩
  intro a b
  let x := PolicyCollision.rawScalar p f ρ a
  let y := PolicyCollision.rawScalar p f ρ b
  have ha := (raw_total p f Γ ρ a).2
  have hb := (raw_total p f Γ ρ b).2
  have haa := eraser_scalar p f hf ρ a a x x ha ha
  have hbb := eraser_scalar p f hf ρ b b y y hb hb
  have hab := eraser_scalar p f hf ρ a b x y ha hb
  have hba := eraser_scalar p f hf ρ b a y x hb ha
  have hl := eraser_scalar p f hf ρ _ _ _ _ haa hbb
  have hr := eraser_scalar p f hf ρ _ _ _ _ hab hba
  have el : PolicyCollision.rawScalar p f ρ (detectorLeft a b) = PolicyCollision.leftValue f x y :=
    CompositeEraser.scalarUniqueness p f Γ _ _ _ _ (raw_total p f Γ ρ _).2 hl
  have er : PolicyCollision.rawScalar p f ρ (detectorRight a b) = PolicyCollision.rightValue f x y :=
    CompositeEraser.scalarUniqueness p f Γ _ _ _ _ (raw_total p f Γ ρ _).2 hr
  refine ⟨el,er,?_⟩
  rw [el,er]
  exact (PolicyCollision.numericCollision f hf).2 x y
#audit_namespace LogicLineages.ControlSensitivityCurrent.FullCollision
end LogicLineages.ControlSensitivityCurrent.FullCollision
