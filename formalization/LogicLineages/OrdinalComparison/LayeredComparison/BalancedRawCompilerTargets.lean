module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Targets

/-- Exact structural recursion, not an equation supplied as a premise.
The leaf is a literal actual BASE comparison, including reversed strict
order and falsity for all other desired signs. The child shape/certificate
laws connect the recursion on Γ to the ACTUAL numeric query tuples. -/
def ExactFiniteCallEquation : Prop :=
  (∀ (C E F : Nat) (desired : Int),
    compileCode [] C E F desired = baseCode E F desired) ∧
  (∀ (C : Nat) (E F : CommonLayerSyntax.BaseTerm) (desired : Int),
    compileCode [] C E.encode F.encode desired = (baseFormula E F desired).encode ∧
    ∀ ν : Nat → Nat,
      ((baseFormula E F desired).eval ν ↔
        Int.sign ((E.value ν : Int) - (F.value ν : Int)) = desired)) ∧
  (∀ (k : Nat) (Γ : List Nat) (C E F : Nat) (desired : Int),
    (children (k :: Γ,C,E,F,desired)).length =
      (BalancedSourceAdapter.formulaCode k E F desired).length ∧
    ∀ a ∈ children (k :: Γ,C,E,F,desired),
      a.1 = Γ ∧ a.2.1 = BalancedSourceAdapter.lowerCertificate C) ∧
  (∀ (a b : Input), b ∈ children a → measure b < measure a) ∧
  (∀ a : Input, recursiveCode a = assemble a ((children a).map recursiveCode))

/-- Concrete algorithms for every actual interface, uniformly on ALL raw
shapes, certificates, source codes, desired integers and result lists.
No source validity, lower comparator, computability witness or correctness
premise is supplied by the caller. -/
def NumericalInterfaces : Prop :=
  Computable (fun p : Nat × Nat × Int => baseCode p.1 p.2.1 p.2.2) ∧
  Computable children ∧
  Computable₂ assemble ∧
  Computable measure

/-- The unchanged finite-frontier graph computes the specific structural
constructor, and that constructor is uniformly computable on every raw
input. Typed positive-level formula calibration, semantic/support induction
and quantified BASE decision are separate, still-pending obligations. -/
def AllCodeComputation : Prop :=
  (∀ a : Input,
    FiniteGraph.graph children assemble measure a (measure a + 1) = [(a,recursiveCode a)]) ∧
  Computable recursiveCode

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Targets
