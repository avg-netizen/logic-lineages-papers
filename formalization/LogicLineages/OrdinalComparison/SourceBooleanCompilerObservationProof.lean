module
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerTargets
public import LogicLineages.OrdinalComparison.SourceExistentialPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanCompiler.Proof
open OriginalDomain GroundEquivalence PrimitiveLowering
open SourceCollisionCompletion SourceCollisionCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem source_positive {Γ} (t : Input Γ .ground) (ρ : Variable Γ .ground → Nat) :
    0<rawScalar (valuation (UnitObservation.substitution ρ)) t.term := by
  obtain ⟨v,hv,hs⟩ := actualScalarTotal Γ t.term
  exact (hs (UnitObservation.substitution ρ)).2

theorem source_observed (Γ : List Ty) (t : Input Γ .ground) (ρ : Variable Γ .ground → Nat) :
    ∃ v : OrdinalVector Γ 0,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t.term=some v ∧
      denote (valuation (UnitObservation.substitution ρ)) (v 0)=((sourceValue ρ t+1 : Nat) : Ordinal) := by
  obtain ⟨v,hv,hs⟩ := actualScalarTotal Γ t.term
  refine ⟨v,hv,?_⟩
  have hh := hs (UnitObservation.substitution ρ)
  have hn : rawScalar (valuation (UnitObservation.substitution ρ)) t.term-1+1=
      rawScalar (valuation (UnitObservation.substitution ρ)) t.term := by omega
  simpa only [sourceValue,hn] using hh.1

theorem call_exact (Γ : List Ty) (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground) :
    (call h x).term=.app (h.term.rename (emptyRename Γ)) (.var x) ∧
    (call h x).specs.length=h.specs.length+2 := by
  constructor
  · unfold call
    rw [(ScopedDAG.Proof.application Γ .ground .ground _ _).1,
      (ScopedDAG.Proof.«renaming» [] Γ (.arrow .ground .ground) (emptyRename Γ) h).1]
    rfl
  · unfold call
    rw [(ScopedDAG.Proof.application Γ .ground .ground _ _).2,
      (ScopedDAG.Proof.«renaming» [] Γ (.arrow .ground .ground) (emptyRename Γ) h).2]
    rfl

theorem sourceObservations : Targets.SourceObservations := ⟨source_observed,call_exact⟩

theorem raw_variable {Γ} (ρ : Variable Γ .ground → Nat) (x : Variable Γ .ground) :
    rawScalar (valuation (UnitObservation.substitution ρ)) (.var x)=ρ x+1 := by
  apply raw_of_assignment _ _ (fun i => .var ⟨.ground,x,i⟩) (ρ x+1) rfl
  change valuation (UnitObservation.substitution ρ) ⟨.ground,x,0⟩=_
  rw [ExistentialPlan.Proof.valuation_inputs]
  rfl

theorem observation_binding {Γ} (ρ : Variable Γ .ground → Nat) (t : Input Γ .ground) (n : Nat) :
    SourceAdditionCompletion.Equation (ExistentialPlan.inputs (ExistentialPlan.extend ρ n))
      (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t).term (ScopedDAG.variableInput (.here : Variable (.ground::Γ) .ground)).term ↔
      n=sourceValue ρ t := by
  rw [(ScopedDAG.Proof.«renaming» Γ (.ground::Γ) .ground (Renaming.weaken Γ .ground) t).1,
    ExistentialPlan.Proof.equation_raw]
  rw [ExistentialPlan.Proof.raw_rename (Renaming.weaken Γ .ground) t.term ρ
    (ExistentialPlan.extend ρ n) (fun _ => rfl)]
  change rawScalar (valuation (UnitObservation.substitution ρ)) t.term=
    rawScalar (valuation (UnitObservation.substitution (ExistentialPlan.extend ρ n))) (.var .here) ↔ _
  rw [raw_variable]
  have hp := source_positive t ρ
  change rawScalar (valuation (UnitObservation.substitution ρ)) t.term=n+1 ↔
    n=rawScalar (valuation (UnitObservation.substitution ρ)) t.term-1
  omega

theorem add_binding {Γ} (ρ : Variable Γ .ground → Nat) (a b : Port Γ) (n : Nat) :
    (Gate.add (ExistentialPlan.portRename (Renaming.weaken Γ .ground) a)
      (ExistentialPlan.portRename (Renaming.weaken Γ .ground) b) (.var .here)).Holds
        (ExistentialPlan.inputs (ExistentialPlan.extend ρ n)) ↔
      n=a.value (ExistentialPlan.inputs ρ)+b.value (ExistentialPlan.inputs ρ) := by
  simp only [Gate.Holds,ExistentialPlan.Proof.port_rename (Renaming.weaken Γ .ground) ρ
    (ExistentialPlan.extend ρ n) (fun _ => rfl)]
  exact eq_comm
end LogicLineages.OrdinalComparison.Source.BooleanCompiler.Proof
