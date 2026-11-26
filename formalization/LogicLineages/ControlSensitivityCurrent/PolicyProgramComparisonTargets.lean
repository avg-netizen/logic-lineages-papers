module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan
/-- Fresh generic predicates; deliberately not the old default-policy Strict/Weak. -/
def Strict (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (a b : OriginalTerm Γ .ground) : Prop :=
  ∀ ρ : Variable Γ .ground → Nat,
    PolicyCollision.rawScalar p f (inputs ρ) a < PolicyCollision.rawScalar p f (inputs ρ) b
def Weak (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (a b : OriginalTerm Γ .ground) : Prop :=
  ∀ ρ : Variable Γ .ground → Nat,
    PolicyCollision.rawScalar p f (inputs ρ) a ≤ PolicyCollision.rawScalar p f (inputs ρ) b
/-- Literal reversed aggregate strict pair, and actual K/I weak wrapper, at one shared valuation. -/
def Pointwise : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (q : Plan Γ)
    (ρ : Variable (compile q).context .ground → Nat),
  (PolicyCollision.rawScalar p f (inputs ρ) (strictPair q).1.term <
    PolicyCollision.rawScalar p f (inputs ρ) (strictPair q).2.term ↔
      ¬ PolicyPlan.ResultHolds p f (compile q) ρ) ∧
  (PolicyCollision.rawScalar p f (inputs ρ) (weakPair q).1.term ≤
    PolicyCollision.rawScalar p f (inputs ρ) (weakPair q).2.term ↔
      ¬ PolicyPlan.ResultHolds p f (compile q) ρ)
/-- Genuine universal comparison against existence of an original shared ground valuation. -/
def Comparison : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (q : BooleanCompiler.Program Γ),
  (Strict p f (BooleanCompiler.strictPair q).1.term (BooleanCompiler.strictPair q).2.term ↔
    ¬ ∃ ρ, InputNormalization.programEval p f ρ q) ∧
  (Weak p f (BooleanCompiler.weakPair q).1.term (BooleanCompiler.weakPair q).2.term ↔
    ¬ ∃ ρ, InputNormalization.programEval p f ρ q)
/-- Real primitive source-DAG reconstruction and exact six-node overhead. -/
def WrapperSyntax : Prop := ∀ (Γ : List Ty) (d : Input Γ .ground),
  (upperInput d).term = GroundEquivalence.upper d.term ∧
  (lowerInput d).term = GroundEquivalence.lower d.term ∧
  (upperInput d).specs.length = d.specs.length + 6 ∧
  (lowerInput d).specs.length = d.specs.length + 6
/-- Actual output tables, not a serialized bit-complexity assertion. -/
def OutputSizes : Prop := ∀ (Γ : List Ty) (q : BooleanCompiler.Program Γ),
  (BooleanCompiler.strictPair q).1.specs.length ≤ BooleanCompiler.budget q ∧
  (BooleanCompiler.strictPair q).2.specs.length ≤ BooleanCompiler.budget q ∧
  (BooleanCompiler.weakPair q).1.specs.length ≤ BooleanCompiler.budget q ∧
  (BooleanCompiler.weakPair q).2.specs.length ≤ BooleanCompiler.budget q
end LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonTargets
