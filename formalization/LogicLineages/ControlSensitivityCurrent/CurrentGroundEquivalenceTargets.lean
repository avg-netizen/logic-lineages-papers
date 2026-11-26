module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalenceDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalenceTargets

open LogicLineages.OrdinalComparison.Source GroundEquivalence ExistentialPlan
open RawSourceDAG PolicyProgramComparisonTargets CurrentGroundEquivalence

def Effective : Prop :=
  Computable (fun p : Bool × Nat × Code × Code => counterexampleCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Computable (fun p : Bool × Nat × Code × Code => reduce p.1 p.2.1 p.2.2.1 p.2.2.2)

def ExactReductions : Prop :=
  ∀ (n : Nat) (a b : Input (List.replicate n Ty.ground) .ground),
    let qw := counterexample true a b
    let qs := counterexample false a b
    let pw := InputNormalization.normalize .nil qw
    let ps := InputNormalization.normalize .nil qs
    let ca := encode ⟨List.replicate n Ty.ground,.ground,a⟩
    let cb := encode ⟨List.replicate n Ty.ground,.ground,b⟩
    counterexampleCode true n ca cb = InputCompiler.encodeInput qw ∧
    counterexampleCode false n ca cb = InputCompiler.encodeInput qs ∧
    reduce true n ca cb = RawPlanComparisonTargets.encodeComparison (BooleanCompiler.strictPair pw) ∧
    reduce false n ca cb = RawPlanComparisonTargets.encodeComparison (BooleanCompiler.weakPair ps) ∧
    (∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f → ∀ p : AdmissibleSum.Policy,
      (Weak p f a.term b.term ↔
        Strict p f (BooleanCompiler.strictPair pw).1.term (BooleanCompiler.strictPair pw).2.term) ∧
      (Strict p f a.term b.term ↔
        Weak p f (BooleanCompiler.weakPair ps).1.term (BooleanCompiler.weakPair ps).2.term)) ∧
    (∀ τ ∈ (compile (BooleanCompiler.lower pw)).context, τ = Ty.ground) ∧
    (∀ τ ∈ (compile (BooleanCompiler.lower ps)).context, τ = Ty.ground) ∧
    let budget := 60000 * (max a.specs.length b.specs.length + 1) + 7
    (BooleanCompiler.strictPair pw).1.specs.length ≤ budget ∧
    (BooleanCompiler.strictPair pw).2.specs.length ≤ budget ∧
    (BooleanCompiler.weakPair ps).1.specs.length ≤ budget ∧
    (BooleanCompiler.weakPair ps).2.specs.length ≤ budget

def Complete : Prop := Effective ∧ ExactReductions

end LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalenceTargets
