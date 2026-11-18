module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonTargets
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CompilerCompositionTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan PolicyProgramComparisonTargets
/-- Actual outputs for the complete explicit existential-prefix/QF AST syntax. -/
def ASTCorrect : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (s : SourceAST.Sentence),
  (Strict p f (BooleanCompiler.strictPair s.matrix.toProgram).1.term
    (BooleanCompiler.strictPair s.matrix.toProgram).2.term ↔ ¬ s.holds p f) ∧
  (Weak p f (BooleanCompiler.weakPair s.matrix.toProgram).1.term
    (BooleanCompiler.weakPair s.matrix.toProgram).2.term ↔ ¬ s.holds p f)
/-- Shared interleaved formula DAG is normalized directly, never via tree expansion. -/
def SharedCorrect : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (n : Nat)
    (q : InputNormalization.Input (List.replicate n Ty.ground) 0),
  let r := InputNormalization.normalize .nil q
  (Strict p f (BooleanCompiler.strictPair r).1.term (BooleanCompiler.strictPair r).2.term ↔
    ¬ ∃ ρ, q.eval p f ρ Fin.elim0) ∧
  (Weak p f (BooleanCompiler.weakPair r).1.term (BooleanCompiler.weakPair r).2.term ↔
    ¬ ∃ ρ, q.eval p f ρ Fin.elim0)
/-- Every original natural coordinate is retained in the actual forest witness valuation. -/
def Retention : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (n : Nat)
    (q : InputNormalization.Input (List.replicate n Ty.ground) 0)
    (ρ : Variable (List.replicate n Ty.ground) .ground → Nat),
  let r := compile (BooleanCompiler.lower (InputNormalization.normalize .nil q))
  (q.eval p f ρ Fin.elim0 ↔ ∃ ν : Variable r.context .ground → Nat,
    (∀ x, ν (r.embedding x) = ρ x) ∧ PolicyPlan.ResultHolds p f r ν) ∧
  (∀ σ ∈ r.context, σ = Ty.ground)
/-- Literal final tables, AST occurrence versus shared-DAG budget explicitly distinguished. -/
def OutputBudgets : Prop :=
  (∀ s : SourceAST.Sentence,
    let q := s.matrix.toProgram
    (∀ σ ∈ (compile (BooleanCompiler.lower q)).context, σ = Ty.ground) ∧
    (BooleanCompiler.strictPair q).1.specs.length ≤ 10000*(s.matrix.cost+1)*(s.matrix.sourceMax+1)+7 ∧
    (BooleanCompiler.strictPair q).2.specs.length ≤ 10000*(s.matrix.cost+1)*(s.matrix.sourceMax+1)+7 ∧
    (BooleanCompiler.weakPair q).1.specs.length ≤ 10000*(s.matrix.cost+1)*(s.matrix.sourceMax+1)+7 ∧
    (BooleanCompiler.weakPair q).2.specs.length ≤ 10000*(s.matrix.cost+1)*(s.matrix.sourceMax+1)+7) ∧
  ∀ (n : Nat) (q : InputNormalization.Input (List.replicate n Ty.ground) 0),
    let r := InputNormalization.normalize .nil q
    (∀ σ ∈ (compile (BooleanCompiler.lower r)).context, σ = Ty.ground) ∧
    (BooleanCompiler.strictPair r).1.specs.length ≤ 10000*q.cost*(q.sourceMax+1)+7 ∧
    (BooleanCompiler.strictPair r).2.specs.length ≤ 10000*q.cost*(q.sourceMax+1)+7 ∧
    (BooleanCompiler.weakPair r).1.specs.length ≤ 10000*q.cost*(q.sourceMax+1)+7 ∧
    (BooleanCompiler.weakPair r).2.specs.length ≤ 10000*q.cost*(q.sourceMax+1)+7
end LogicLineages.ControlSensitivityCurrent.CompilerCompositionTargets
