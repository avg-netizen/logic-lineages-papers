module
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationDefinitions
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence PrimitiveLowering ExistentialPlan BooleanCompiler
/-- Genuine successful selected-policy assignment and literal supplied unary call. -/
def Observations : Prop :=
  (∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
    (ρ : Variable Γ .ground → Nat) (t : Input Γ .ground),
    ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment p t.term = some v ∧
      ParametricSourceSuccessor.denoteWith f
        (fun c => ((inputs ρ c + 1 : Nat) : Ordinal)) (v 0) =
          ((InputNormalization.sourceValue p f ρ t + 1 : Nat) : Ordinal)) ∧
  ∀ (Γ : List Ty) (h : Input [] (.arrow .ground .ground)) (x : Variable Γ .ground),
    (call h x).term = .app (h.term.rename (emptyRename Γ)) (.var x) ∧
    (call h x).specs.length = h.specs.length + 2
/-- Fresh positive raw coordinate is n+1, not n; no success oracle is assumed. -/
def ObservationBinder : Prop :=
  (∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
    (ρ : Variable Γ .ground → Nat) (t : Input Γ .ground) (n : Nat),
    PolicyAddition.Equation p f (inputs (extend ρ n))
      (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t).term
      (ScopedDAG.variableInput (Variable.here : Variable (.ground::Γ) .ground)).term ↔
        n = InputNormalization.sourceValue p f ρ t) ∧
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
    (ρ : Variable Γ .ground → Nat) (t : Input Γ .ground) (q : Plan (.ground::Γ)),
    PolicyPlan.Eval p f ρ (.existsGround (.equation
      (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t)
      (ScopedDAG.variableInput .here) q)) ↔
    PolicyPlan.Eval p f (extend ρ (InputNormalization.sourceValue p f ρ t)) q
/-- All five literal Program constructors, same actual policy/control and shared coordinates. -/
def Lowering : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : Variable Γ .ground → Nat) (q : Program Γ),
  InputNormalization.programEval p f ρ q ↔ PolicyPlan.Eval p f ρ (lower q)
/-- Real typed source forest, not a symbolic arithmetic predicate replacement. -/
def Forest : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (q : Program Γ),
  (∀ ρ : Variable Γ .ground → Nat,
    InputNormalization.programEval p f ρ q ↔
      ∃ ν : Variable (compile (lower q)).context .ground → Nat,
        (∀ x, ν ((compile (lower q)).embedding x) = ρ x) ∧
        PolicyPlan.ResultHolds p f (compile (lower q)) ν) ∧
  ((∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ σ ∈ (compile (lower q)).context, σ = Ty.ground)
end LogicLineages.ControlSensitivityCurrent.PolicyProgramTargets
