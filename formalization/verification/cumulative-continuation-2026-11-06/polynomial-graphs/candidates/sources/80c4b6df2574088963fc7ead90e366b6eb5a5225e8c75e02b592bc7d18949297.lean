module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets

def ExactAllocation : Prop := ∀ (start : Nat) (t : Expr),
  0 < nodeCount t ∧ (allocated start t).Nodup ∧
    (∀ i, i ∈ allocated start t ↔ start ≤ i ∧ i < start+nodeCount t) ∧
    (Fresh start t → ∀ i ∈ allocated start t, i ∉ t.variables)

def FreshSymbolicOutput : Prop := ∀ (t : Expr) (resultName : Nat),
  Fresh (freshStart t resultName) t ∧ resultName < freshStart t resultName ∧
    resultName ∉ allocated (freshStart t resultName) t

/-- No unbound auxiliary is introduced, and no original name is renamed or
replaced by an independent value. The symbolic result may be an original name. -/
def GraphSupport : Prop :=
  (∀ (start : Nat) (t : Expr) (row : Row), row ∈ rows start t →
    ∀ i ∈ rowVariables row, i ∈ t.variables ∨ i ∈ allocated start t) ∧
  (∀ (t : Expr) (resultName : Nat) (row : Row), row ∈ graphRows t resultName →
    ∀ i ∈ rowVariables row,
      i ∈ t.variables ∨ i = resultName ∨ i ∈ (expressionPackage t resultName).2.1)

/-- Every generated word has its genuine domain on every natural raw input;
the common finite degree bound is the one carried by the emitted package. -/
def ExpressionDomainsAndDegree : Prop := ∀ t : Expr, ValidExpr t →
  3 ≤ exprDegree t ∧
    (∀ (start : Nat) (row : Row), row ∈ rows start t →
      RowAllowed (exprDegree t) row ∧ ∀ ν : Nat → Nat, RowDomain row ν) ∧
    (∀ (resultName : Nat) (row : Row), row ∈ graphRows t resultName →
      RowAllowed (expressionPackage t resultName).1 row ∧
        ∀ ν : Nat → Nat, RowDomain row ν)

def GraphSoundness : Prop := ∀ (start : Nat) (t : Expr), ValidExpr t →
  ∀ ν : Nat → Nat, GraphHolds start t ν → ν (output start t) = t.value ν

def TotalGraphRealization : Prop := ∀ (start : Nat) (t : Expr), ValidExpr t →
  ∀ ν : Nat → Nat, Fresh start t → ∃ σ : Nat → Nat,
    (∀ i, i ∉ allocated start t → σ i = ν i) ∧
      GraphHolds start t σ ∧ σ (output start t) = t.value ν

def AllocatedNodeUniqueness : Prop := ∀ (start : Nat) (t : Expr), ValidExpr t →
  ∀ ν σ : Nat → Nat, (∀ i ∈ t.variables, ν i = σ i) →
    GraphHolds start t ν → GraphHolds start t σ →
      ∀ i ∈ allocated start t, ν i = σ i

/-- Exact correlation for every symbolic result name, including one that
also occurs among the original source variables. Only fresh nodes are bound. -/
def CorrelatedExistentialGraph : Prop := ∀ t : Expr, ValidExpr t →
  ∀ (resultName : Nat) (ν : Nat → Nat),
    expressionGraph t resultName ν ↔ ν resultName = t.value ν

/-- A fresh result symbol gives the total functional graph. If the caller
instead reuses a source symbol, CorrelatedExistentialGraph retains that exact
self-correlation rather than asserting false unconditional satisfiability. -/
def TotalFunctionalGraph : Prop := ∀ t : Expr, ValidExpr t →
  ∀ resultName : Nat, resultName ∉ t.variables → ∀ ν : Nat → Nat,
    ∃! y : Nat, expressionGraph t resultName (Function.update ν resultName y)

def InstructionCodeCalibration : Prop := ∀ t : Expr,
  ExpressionCode.instructions t.encode = instructions t ∧
    (instructions t).length = nodeCount t ∧
    ExpressionCode.originalNames (instructions t) = t.variables ∧
    ExpressionCode.headNames (instructions t) = t.heads

def RowMachineCalibration : Prop :=
  ∀ (t : Expr) (start : Nat) (stack : List Nat) (prior : List Row),
    ExpressionCode.run (instructions t) (start,stack,prior) =
      (start+nodeCount t,output start t::stack,prior++rows start t)

def LiteralGraphCompiler : Prop := ∀ (t : Expr) (resultName : Nat),
  ExpressionCode.package t.encode resultName = expressionPackage t resultName

def ActualNumericProgram : Prop :=
  Primrec ExpressionCode.instructions ∧ Primrec₂ ExpressionCode.run ∧
    Primrec₂ ExpressionCode.package

/-- The complete fixed-expression clause of paper08 thm:graphs. This is an
effective finite existential translation into the literal word alphabet;
it is not a decision procedure for those existential sentences. -/
def FullExpressionGraphs : Prop := ExactAllocation ∧ FreshSymbolicOutput ∧ GraphSupport ∧
  ExpressionDomainsAndDegree ∧ GraphSoundness ∧ TotalGraphRealization ∧
  AllocatedNodeUniqueness ∧ CorrelatedExistentialGraph ∧ TotalFunctionalGraph ∧
  InstructionCodeCalibration ∧ RowMachineCalibration ∧ LiteralGraphCompiler ∧ ActualNumericProgram

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets
