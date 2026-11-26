module
public import LogicLineages.ControlSensitivityCurrent.FullAggregateTargets
public import LogicLineages.ControlSensitivityCurrent.FullCollisionProof
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullAggregate
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PolicyCollision SourceCollisionCompletion SourceAggregateCompletion

private theorem eraser_raw (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground) :
    PolicyCollision.rawScalar p f ρ (eraser a b) =
      PolicyCollision.g f (3*PolicyCollision.rawScalar p f ρ a+PolicyCollision.rawScalar p f ρ b+2) := by
  have ht := (FullCollision.completeCollision f hf p Γ ρ).1
  have hc := FullAddition.completeAddition.2.2.2 f hf
  have he := (CompositeEraser.finiteClosure p f hc.1 (fun n => (hc.2.1 n).le) Γ _ a b _ _ (ht a).2 (ht b).2).1
  have hu := CompositeEraser.scalarUniqueness p f Γ _ _ _ _ (ht (eraser a b)).2 he
  simpa only [PolicyCollision.g,Nat.add_assoc] using hu

private theorem combine (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (a b c d : Nat) (hab : b ≤ a) (hcd : d ≤ c) :
    PolicyCollision.g f (3*b+d+2) ≤ PolicyCollision.g f (3*a+c+2) ∧
    (PolicyCollision.g f (3*a+c+2) = PolicyCollision.g f (3*b+d+2) ↔ a=b ∧ c=d) ∧
    (¬ (a=b ∧ c=d) → 2 ≤ PolicyCollision.g f (3*a+c+2)-PolicyCollision.g f (3*b+d+2)) := by
  have hm : StrictMono (PolicyCollision.g f) := by
    intro x y h
    have hf' := (FullAddition.completeAddition.2.2.2 f hf).1 (show x+2 < y+2 by omega)
    unfold PolicyCollision.g
    omega
  refine ⟨hm.monotone (by omega),?_,?_⟩
  · constructor
    · intro h
      have := hm.injective h
      omega
    · rintro ⟨rfl,rfl⟩
      rfl
  · intro h
    have hn : 3*b+d+2 < 3*a+c+2 := by omega
    have hg := (PolicyCollision.numericCollision f hf).1 (3*b+d+2)
    have hl := hm.monotone (show 3*b+d+2+1 ≤ 3*a+c+2 by omega)
    omega

theorem completeAggregate : Targets.CompleteAggregate := by
  refine ⟨SourceGammaAggregateCode.Proof.exactLiteralCodes,
    SourceGammaAggregateCode.Proof.exactAggregateCode,
    SourceGammaAggregateCode.Proof.uniformPrimitiveRecursive,?_⟩
  intro f hf p Γ ρ es
  induction es with
  | nil => simp [aggregate]
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    have hd := (FullCollision.completeCollision f hf p Γ ρ).2 a b
    have hc := combine f hf
      (PolicyCollision.rawScalar p f ρ (detectorLeft a b))
      (PolicyCollision.rawScalar p f ρ (detectorRight a b))
      (PolicyCollision.rawScalar p f ρ (aggregate es).1)
      (PolicyCollision.rawScalar p f ρ (aggregate es).2) hd.2.2.1 ih.1
    have he :
        (PolicyCollision.rawScalar p f ρ (detectorLeft a b) = PolicyCollision.rawScalar p f ρ (detectorRight a b) ∧
          PolicyCollision.rawScalar p f ρ (aggregate es).1 = PolicyCollision.rawScalar p f ρ (aggregate es).2) ↔
          ∀ e ∈ (a,b)::es, PolicyCollision.rawScalar p f ρ e.1 = PolicyCollision.rawScalar p f ρ e.2 := by
      rw [hd.2.2.2.1,ih.2.1]
      simp
    simp only [aggregate]
    rw [eraser_raw f hf p Γ ρ,eraser_raw f hf p Γ ρ]
    exact ⟨hc.1,hc.2.1.trans he,fun h => hc.2.2 (fun hh => h (he.mp hh))⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.FullAggregate
end LogicLineages.ControlSensitivityCurrent.FullAggregate
