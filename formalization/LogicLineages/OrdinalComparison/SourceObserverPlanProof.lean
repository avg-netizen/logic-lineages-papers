module
public import LogicLineages.OrdinalComparison.SourceObserverPlanTargets
public import LogicLineages.OrdinalComparison.SourceAffinePlanProof
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProof
public import LogicLineages.OrdinalComparison.SourceExistentialPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ObserverPlan.Proof
open GroundEquivalence PrimitiveLowering OriginalDomain
open SourceCollisionCompletion SourceCollisionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem effectiveAnchor : Targets.EffectiveAnchor := by
  refine ⟨AbsoluteObserver.Proof.open_evaluator_computable,?_⟩
  intro Γ τ hΓ t
  obtain ⟨w,s,hw,hs,hcode,hclosed,hopen,hpos,hval⟩ := AbsoluteObserver.Proof.anchorCorrect Γ hΓ τ t.term
  exact ⟨hopen,hopen.symm ▸ hpos⟩

theorem equation_observations {Γ} (ρ : Variable Γ .ground → Nat) (a b : OriginalTerm Γ .ground) :
    SourceAdditionCompletion.Equation (ExistentialPlan.inputs ρ) a b ↔
      ∃ q, AbsoluteObserver.Observation (ExistentialPlan.inputs ρ) a q ∧
        AbsoluteObserver.Observation (ExistentialPlan.inputs ρ) b q := by
  constructor
  · intro he
    have hn := (ExistentialPlan.Proof.equation_raw ρ a b).mp he
    obtain ⟨va,ha,hsa⟩ := actualScalarTotal Γ a
    obtain ⟨vb,hb,hsb⟩ := actualScalarTotal Γ b
    have hpa := hsa (UnitObservation.substitution ρ)
    have hpb := hsb (UnitObservation.substitution ρ)
    let q := rawScalar (valuation (UnitObservation.substitution ρ)) a-1
    have hq : rawScalar (valuation (UnitObservation.substitution ρ)) a=q+1 := by dsimp [q]; omega
    refine ⟨q,⟨va,ha,?_⟩,⟨vb,hb,?_⟩⟩
    · rw [← ExistentialPlan.Proof.valuation_inputs,hpa.1,hq]
    · rw [← ExistentialPlan.Proof.valuation_inputs,hpb.1,← hn,hq]
  · rintro ⟨q,⟨va,ha,hea⟩,⟨vb,hb,heb⟩⟩
    exact ⟨va,vb,ha,hb,hea.trans heb.symm⟩

theorem double_inputs {Γ} (ρ : Variable Γ .ground → Nat) (x y : Nat) :
    ExistentialPlan.inputs (ExistentialPlan.extend (ExistentialPlan.extend ρ y) x)=
      AbsoluteObserver.extend (ExistentialPlan.inputs ρ) x y := by
  funext c
  rcases c with ⟨σ,z,j⟩
  cases z with
  | here => rfl
  | there z => cases z with
    | here => rfl
    | there z => cases σ <;> rfl

theorem linear_at {Γ τ} (ρ : Variable Γ .ground → Nat) (v : Port Γ) (C x y : Nat) :
    ExistentialPlan.Eval (ExistentialPlan.extend (ExistentialPlan.extend ρ y) x)
      (AffinePlan.affinePlan (AbsoluteObserver.factor τ) (AbsoluteObserver.factor τ*C)
        (ExistentialPlan.portRename (AbsoluteObserver.shiftTwo Γ) v) (.var .here) (.var (.there .here))) ↔
      AbsoluteObserver.factor τ*v.value (ExistentialPlan.inputs ρ)+x=AbsoluteObserver.factor τ*C+y := by
  rw [AffinePlan.Proof.affine]
  rw [ExistentialPlan.Proof.port_rename (AbsoluteObserver.shiftTwo Γ) ρ
    (ExistentialPlan.extend (ExistentialPlan.extend ρ y) x) (fun _ => rfl)]
  rfl

theorem formulaExact : Targets.FormulaExact := by
  intro Γ τ hΓ t v ρ
  unfold realize
  rw [(effectiveAnchor.2 Γ τ hΓ t).1]
  change (∃ y x, SourceAdditionCompletion.Equation
    (ExistentialPlan.inputs (ExistentialPlan.extend (ExistentialPlan.extend ρ y) x))
      (AbsoluteProbeDAG.originalInput t).term (AbsoluteProbeDAG.closedInput hΓ t).term ∧
    ExistentialPlan.Eval (ExistentialPlan.extend (ExistentialPlan.extend ρ y) x)
      (AffinePlan.affinePlan (AbsoluteObserver.factor τ) (AbsoluteObserver.factor τ*AbsoluteObserver.anchor hΓ t.term)
        (ExistentialPlan.portRename (AbsoluteObserver.shiftTwo Γ) v) (.var .here) (.var (.there .here)))) ↔ _
  rw [(AbsoluteProbeDAG.Proof.original Γ τ t).1,(AbsoluteProbeDAG.Proof.closed Γ τ hΓ t).1]
  simp only [linear_at,equation_observations]
  simp only [double_inputs,AbsoluteObserver.Formula]
  constructor
  · rintro ⟨y,x,⟨q,ha,hb⟩,he⟩
    exact ⟨x,y,q,ha,hb,by omega⟩
  · rintro ⟨x,y,q,ha,hb,he⟩
    exact ⟨y,x,⟨q,ha,hb⟩,by omega⟩

theorem observerExact : Targets.ObserverExact := by
  intro Γ τ hΓ t v ρ
  rw [formulaExact]
  have hh := AbsoluteObserver.Proof.fullAbsoluteObserver.2.2.2.2 Γ hΓ τ t.term
    (ExistentialPlan.inputs ρ) (v.value (ExistentialPlan.inputs ρ))
  simpa only [← ExistentialPlan.Proof.valuation_inputs] using hh
end LogicLineages.OrdinalComparison.Source.ObserverPlan.Proof
