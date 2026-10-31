module
public import LogicLineages.OrdinalComparison.SourceGroundArithmeticCounterTargets
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerObservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter.Proof
open GroundEquivalence BooleanCompiler OriginalDomain SourceCollisionCompletion
open ForwardTranslation LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem observed_weaken {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (b : Input Γ .ground) :
    sourceValue (ExistentialPlan.extend ρ n) (ScopedDAG.renameInput (Renaming.weaken Γ .ground) b)=sourceValue ρ b := by
  unfold sourceValue
  rw [(ScopedDAG.Proof.«renaming» _ _ _ _ _).1,
    ExistentialPlan.Proof.raw_rename (Renaming.weaken Γ .ground) b.term ρ
      (ExistentialPlan.extend ρ n) (fun _ => rfl)]

theorem pointwise : Targets.Pointwise := by
  intro Γ ρ strict a b
  have ha := BooleanCompiler.Proof.source_positive a ρ
  have hb := BooleanCompiler.Proof.source_positive b ρ
  simp only [counter,Eval,observed_weaken]
  cases strict <;>
    simp [BooleanWire.evaluate,BooleanWire.evalNode,
      PrimitiveLowering.Port.value,ExistentialPlan.inputs,SourceSortCompletion.input,
      ExistentialPlan.extend,RawQuery,sourceValue] <;> omega

theorem unsatisfiable : Targets.Unsatisfiable := by
  intro Γ strict a b
  have hp (ρ : Variable Γ .ground → Nat) := pointwise Γ ρ strict a b
  simp only [hp]
  cases strict <;> simp [RawQuery,GroundEquivalence.Strict,GroundEquivalence.Weak]

theorem groundQuery : Targets.GroundQuery := by
  intro Γ ρ strict a b
  obtain ⟨av,ha,hsa⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ a.term
  obtain ⟨bv,hb,hsb⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ b.term
  have hq : GroundPositiveQuerySplit.QueryAt strict a.term b.term (ExistentialPlan.inputs ρ) ↔
      SourceComparisonAt strict av bv (fun c => ExistentialPlan.inputs ρ c+1) := by
    constructor
    · rintro ⟨ax,bx,hax,hbx,h⟩
      rw [ha] at hax
      rw [hb] at hbx
      cases Option.some.inj hax
      cases Option.some.inj hbx
      exact h
    · intro h
      exact ⟨av,bv,ha,hb,h⟩
  have hsa0 : sourceVectorAtValue av (fun c => ExistentialPlan.inputs ρ c+1) 0 =
      (rawScalar (valuation (UnitObservation.substitution ρ)) a.term : Ordinal) := by
    change denote (fun c => ((ExistentialPlan.inputs ρ c+1 : Nat) : Ordinal)) (av 0)=_
    rw [← ExistentialPlan.Proof.valuation_inputs]
    exact (hsa (UnitObservation.substitution ρ)).1
  have hsb0 : sourceVectorAtValue bv (fun c => ExistentialPlan.inputs ρ c+1) 0 =
      (rawScalar (valuation (UnitObservation.substitution ρ)) b.term : Ordinal) := by
    change denote (fun c => ((ExistentialPlan.inputs ρ c+1 : Nat) : Ordinal)) (bv 0)=_
    rw [← ExistentialPlan.Proof.valuation_inputs]
    exact (hsb (UnitObservation.substitution ρ)).1
  have hz : ∀ j : Nat, sourceVectorAtValue av (fun c => ExistentialPlan.inputs ρ c+1) (j+1) ≤
      sourceVectorAtValue bv (fun c => ExistentialPlan.inputs ρ c+1) (j+1) := by
    intro j
    simp [sourceVectorAtValue,ordinalVectorAt,denote]
  rw [hq,SourceComparisonAt,hsa0,hsb0]
  cases strict <;> simp only [hz,forall_const,true_and,RawQuery,Bool.false_eq_true,if_false,if_true,Nat.cast_lt,Nat.cast_le]
end LogicLineages.OrdinalComparison.Source.GroundArithmeticCounter.Proof
