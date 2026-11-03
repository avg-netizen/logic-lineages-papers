module
public import LogicLineages.OrdinalComparison.ActualArithmeticCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode.Targets
open Arithmetic

def ExactExpressionLift : Prop := ∀ (k : Nat) (a : Expr),
  liftCode k (exprCode a) = exprCode (a.lift k)

def ExactFormulaConstructors : Prop :=
  (∀ (xs : List Formula), conjunctionCode (xs.map formulaCode) = formulaCode (conjunction xs)) ∧
  (∀ (xs : List Formula), disjunctionCode (xs.map formulaCode) = formulaCode (disjunction xs)) ∧
  (∀ (Γ : List Ty) (h : ∀ σ ∈ Γ, σ=Ty.ground) (t : OriginalTerm Γ .ground)
      (xs : List Expr) (y : Expr),
    observationCode Γ.length (SyntaxCode.encodeTerm t) (xs.map exprCode) (exprCode y) =
      formulaCode (.observation h t xs y))

def ExactFixedControl : Prop :=
  (∀ (a b : Expr), successorCode (exprCode a) (exprCode b) = formulaCode (successor a b)) ∧
  (∀ (a b : Expr), phiCode (exprCode a) (exprCode b) = formulaCode (phi a b)) ∧
  (∀ (n : Nat) (a b : Expr), phiChainCode n (exprCode a) (exprCode b) = formulaCode (phiChain n a b))

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec numeralCode ∧ Primrec variableCode ∧ Primrec₂ addCode ∧ Primrec₂ scaleCode ∧
  Primrec₂ liftCode ∧ Primrec₂ eqCode ∧ Primrec₂ leCode ∧
  Primrec (fun p : Nat×Nat×List Nat×Nat => observationCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec₂ andCode ∧ Primrec₂ orCode ∧ Primrec existsCode ∧
  Primrec conjunctionCode ∧ Primrec disjunctionCode ∧
  Primrec₂ successorCode ∧ Primrec₂ phiCode ∧
  Primrec (fun p : Nat×Nat×Nat => phiChainCode p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode.Targets
