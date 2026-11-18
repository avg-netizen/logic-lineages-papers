module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationProof
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanSemanticProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgram
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence PrimitiveLowering ExistentialPlan BooleanCompiler

theorem observations : PolicyProgramTargets.Observations := by
  constructor
  · intro p f Γ ρ t
    exact (PolicyObservation.observationCalibration p f Γ (inputs ρ) t.term).2
  · intro Γ h x
    constructor
    · unfold call
      rw [(ScopedDAG.Proof.application Γ .ground .ground _ _).1,
        (ScopedDAG.Proof.«renaming» [] Γ (.arrow .ground .ground) (emptyRename Γ) h).1]
      rfl
    · unfold call
      rw [(ScopedDAG.Proof.application Γ .ground .ground _ _).2,
        (ScopedDAG.Proof.«renaming» [] Γ (.arrow .ground .ground) (emptyRename Γ) h).2]
      rfl

theorem raw_variable (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) (x : Variable Γ .ground) :
    PolicyCollision.rawScalar p f (inputs ρ) (.var x) = ρ x + 1 := by
  unfold PolicyCollision.rawScalar
  change OriginalDomain.finiteValue ((ρ x + 1 : Nat) : Ordinal) = ρ x + 1
  exact OriginalDomain.originalFiniteValueCalibration _

theorem observation_binding (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) (t : Input Γ .ground) (n : Nat) :
    PolicyAddition.Equation p f (inputs (extend ρ n))
      (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t).term
      (ScopedDAG.variableInput (Variable.here : Variable (.ground::Γ) .ground)).term ↔
      n = InputNormalization.sourceValue p f ρ t := by
  rw [PolicyObservation.equationCalibration,
    (ScopedDAG.Proof.«renaming» Γ (.ground::Γ) .ground (Renaming.weaken Γ .ground) t).1]
  have hc : ∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
      inputs (extend ρ n) ⟨τ,Renaming.weaken Γ .ground x,j⟩ = inputs ρ ⟨τ,x,j⟩ := by
    intro τ x j
    cases τ with
    | ground => rfl
    | arrow a b => rfl
  rw [PolicyObservation.sourceNaturality p f Γ (.ground::Γ)
    (Renaming.weaken Γ .ground) (inputs ρ) (inputs (extend ρ n)) hc t.term]
  change PolicyCollision.rawScalar p f (inputs ρ) t.term =
    PolicyCollision.rawScalar p f (inputs (extend ρ n)) (.var .here) ↔ _
  rw [raw_variable]
  have hp := (PolicyObservation.observationCalibration p f Γ (inputs ρ) t.term).1
  change PolicyCollision.rawScalar p f (inputs ρ) t.term = n+1 ↔
    n = PolicyCollision.rawScalar p f (inputs ρ) t.term-1
  omega

theorem observationBinder : PolicyProgramTargets.ObservationBinder := by
  refine ⟨fun p f Γ ρ t n => observation_binding p f ρ t n, ?_⟩
  intro p f Γ ρ t q
  change (∃ n, PolicyAddition.Equation p f (inputs (extend ρ n)) _ _ ∧
    PolicyPlan.Eval p f (extend ρ n) q) ↔ _
  simp only [observation_binding,exists_eq_left]

theorem add_binding {Γ} (ρ : Variable Γ .ground → Nat) (a b : Port Γ) (n : Nat) :
    (Gate.add (portRename (Renaming.weaken Γ .ground) a)
      (portRename (Renaming.weaken Γ .ground) b) (.var .here)).Holds
        (inputs (extend ρ n)) ↔ n = a.value (inputs ρ)+b.value (inputs ρ) := by
  simp only [Gate.Holds,PolicyPlan.port_rename (Renaming.weaken Γ .ground) ρ
    (extend ρ n) (fun _ => rfl)]
  exact eq_comm
end LogicLineages.ControlSensitivityCurrent.PolicyProgram
