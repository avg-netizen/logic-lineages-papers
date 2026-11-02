module
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Targets
open ForwardTranslation Arithmetic ArithmeticCode FormulaConstruction

def ExactGenuineConstants : Prop := ∀ (a : ClosedPositive) (c δ : Nat),
  headNormCode (closedPositiveCode a) = actualOrdinalNorm (fixedHead a) ∧
  shiftedNormCode (closedPositiveCode a) δ = actualOrdinalNorm (shiftedHead a δ) ∧
  rayBaseCode (closedPositiveCode a) c = ActualUnaryRay.totalNorm a c 0 ∧
  thresholdCode (closedPositiveCode a) c δ = threshold a c δ ∧
  ∀ t : Nat, actualOrdinalNorm (shiftedHead a δ) ≤ t →
    prefixValueCode (closedPositiveCode a) δ t = actualHeadValue (shiftedHead a δ) t

def ExactFormulaCompilation : Prop := ∀ (Γ : List Ty) (q : UnitElimination.Tree Nat (.ground::Γ))
    (a : ClosedPositive) (c δ : Nat) (t y : Expr),
  graphCode Γ.length (closedPositiveCode a) c δ (UnitEliminationTreeCode.code q) (exprCode t) (exprCode y) =
    formulaCode (graph q a c δ t y)

def EffectiveAlgorithms : Prop := Primrec₂ raySourceCode ∧ Computable₂ constantsCode ∧
  Computable (fun p : Nat×Nat×Nat×Nat×Nat×Nat×Nat =>
    graphCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) ∧
  Computable (fun p : List Nat×Nat×Nat×Nat×Nat => compileCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- An actual unary source supplies every constant and literal ray observation.
The compiler returns the entire genuine graph, not only its eventual tail. -/
def ActualEffectiveWholeGraph : Prop := ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)),
  ∃ (u : OrdinalVector Γ (Ty.curriedGround 1).level) (a : ClosedPositive) (c : Nat)
      (q : UnitElimination.Tree (Nat×Nat) (.ground::Γ)),
    ActualUnaryRay.Constants K u a c ∧
    raySourceCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) = SyntaxCode.encodeTerm (ActualUnaryRay.source K) ∧
    UnitElimination.build ((.ground::Γ).length+1) (ActualUnaryRay.source K) = some q ∧
    constantsCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) =
      some (closedPositiveCode a,c,UnitEliminationTreeCode.code (UnitElimination.realize q)) ∧
    ∀ (δ : Nat) (t y : Expr),
      compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) δ (exprCode t) (exprCode y) =
        some (formulaCode (graph (UnitElimination.realize q) a c δ t y)) ∧
      ∀ ν : Nat → Nat, (graph (UnitElimination.realize q) a c δ t y).eval ν ↔
        actualOrdinalNorm (shiftedHead a δ) ≤ t.value ν ∧
        y.value ν = actualHeadValue (shiftedHead a δ) (t.value ν)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Targets
