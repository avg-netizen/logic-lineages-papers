module
public import LogicLineages.OrdinalComparison.SourceDecisionEquivalenceTargets
public import LogicLineages.OrdinalComparison.SourceBooleanPlanProof
public import LogicLineages.OrdinalComparison.SourceBinaryPlanProof
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof
public import LogicLineages.OrdinalComparison.SourceObserverPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
open GroundEquivalence PrimitiveLowering

theorem numeric_effective : Computable numericData := by
  have hf := GroundPositiveQuerySplit.Proof.flagPrimitiveRecursive.to_comp
  have ha : Computable (fun p : Nat×Nat×Nat => AbsoluteObserver.openSourceValue (p.1,p.2.1)) := AbsoluteObserver.Proof.open_evaluator_computable.comp
    (Computable.fst.pair (Computable.fst.comp Computable.snd))
  have hb : Computable (fun p : Nat×Nat×Nat => AbsoluteObserver.openSourceValue (p.1,p.2.2)) := AbsoluteObserver.Proof.open_evaluator_computable.comp
    (Computable.fst.pair (Computable.snd.comp Computable.snd))
  exact hf.pair (ha.pair hb)

theorem join_correct (Γ : List Ty) (p : ExistentialPlan.Plan Γ) :
    ∀ (q : ExistentialPlan.Plan Γ) (ρ : Variable Γ .ground → Nat),
      ExistentialPlan.Eval ρ (join p q) ↔ ExistentialPlan.Eval ρ p ∧ ExistentialPlan.Eval ρ q := by
  induction p with
  | done => intro q ρ; simp only [join,ExistentialPlan.Eval,true_and]
  | equation a b p ih =>
    intro q ρ
    simp only [join,ExistentialPlan.Eval,ih,and_assoc]
  | gate g p ih =>
    intro q ρ
    simp only [join,ExistentialPlan.Eval,ih,and_assoc]
  | @existsGround Γ p ih =>
    intro q ρ
    change (∃ n, ExistentialPlan.Eval (ExistentialPlan.extend ρ n)
      (join p (BinaryPlan.renamePlan (Renaming.weaken Γ .ground) q))) ↔
      (∃ n, ExistentialPlan.Eval (ExistentialPlan.extend ρ n) p) ∧ ExistentialPlan.Eval ρ q
    have hr (n : Nat) := BinaryPlan.Proof.renameCorrect Γ (.ground::Γ) (Renaming.weaken Γ .ground)
      ρ (ExistentialPlan.extend ρ n) (fun _ => rfl) q
    simp only [ih,hr]
    constructor
    · rintro ⟨n,hp,hq⟩
      exact ⟨⟨n,hp⟩,hq⟩
    · rintro ⟨⟨n,hp⟩,hq⟩
      exact ⟨n,hp,hq⟩

theorem order_correct {Γ} (strict : Bool) (a b : Port Γ) (ρ : Variable Γ .ground → Nat) :
    ExistentialPlan.Eval ρ (orderPlan strict a b) ↔
      ¬ (if strict then a.value (ExistentialPlan.inputs ρ)<b.value (ExistentialPlan.inputs ρ)
        else a.value (ExistentialPlan.inputs ρ)≤b.value (ExistentialPlan.inputs ρ)) := by
  unfold orderPlan
  rw [BooleanPlan.Proof.matrixExact]
  cases strict <;> simp [orderDag,ports,BooleanWire.evaluate,BooleanWire.evalNode]
end LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
