module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence ExistentialPlan CurrentDecision
open RawSourceDAG.InputCompiler (encodeInput)

def GeneralReduction : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (strict : Bool) (n : Nat) (σ τ : Ty)
      (a : Input (List.replicate n Ty.ground) σ) (b : Input (List.replicate n Ty.ground) τ),
      let q : QueryCode := (strict, RawSourceDAG.encode ⟨_,σ,a⟩, RawSourceDAG.encode ⟨_,τ,b⟩)
      ∃ r : InputNormalization.Input (List.replicate (n+6) Ty.ground) 0,
        toArithmetic p f q = (n+6,encodeInput r) ∧
        (Universal p f strict a b ↔ ¬ ∃ ρ, r.eval p f ρ Fin.elim0)

def ArithmeticReduction : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (n : Nat) (q : InputNormalization.Input (List.replicate n Ty.ground) 0),
      let program := InputNormalization.normalize .nil q
      CurrentCompiler.compile (n,encodeInput q) = CurrentCompiler.expected q ∧
      (Ground p f true (BooleanCompiler.strictPair program).1 (BooleanCompiler.strictPair program).2 ↔
        ¬ ∃ ρ, q.eval p f ρ Fin.elim0) ∧
      (Ground p f false (BooleanCompiler.weakPair program).1 (BooleanCompiler.weakPair program).2 ↔
        ¬ ∃ ρ, q.eval p f ρ Fin.elim0)

def GroundSpecialization : Prop :=
  ∀ p f strict (n : Nat) (a b : Input (List.replicate n Ty.ground) .ground),
    Universal p f strict a b ↔ Ground p f strict a b

def Effective : Prop :=
  Computable CurrentCompiler.compile ∧
  ∀ (p : AdmissibleSum.Policy), PolicyShape.Effective p →
    ∀ (f : Nat → Nat), Computable f → FullAddition.Targets.SourceGrowth f →
      Computable (toArithmetic p f) ∧ Computable (fun q => CurrentCompiler.compile (toArithmetic p f q))

def Full : Prop := GeneralReduction ∧ ArithmeticReduction ∧ GroundSpecialization ∧ Effective
end LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
