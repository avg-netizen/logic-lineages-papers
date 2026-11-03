module
public import LogicLineages.OrdinalComparison.ActualHeadGraphFormulaDefinitions
public import LogicLineages.OrdinalComparison.UnitArithmeticFormulaCodeDefinitions
public import LogicLineages.OrdinalComparison.UnitHeadCodeDefinitions
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeDefinitions
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollapseDefinitions
public import LogicLineages.OrdinalComparison.EncodedFiniteTailDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode
open ArithmeticCode ForwardTranslation

def headNormCode (a : Nat) := rawNormCode (encodedClosedHead a)
def shiftedNormCode (a δ : Nat) := headNormCode a+2*δ
def rayBaseCode (a c : Nat) := headNormCode a+c+1
def thresholdCode (a c δ : Nat) := max (shiftedNormCode a δ) (rayBaseCode a c)
def controlIter (δ t : Nat) := (Phi^[δ]) t
noncomputable def prefixValueCode (a δ t : Nat) :=
  encodedCollapseValue (encodedFiniteTail (encodedClosedHead a) (controlIter δ t-headNormCode a))+δ

noncomputable def finitePrefixCode (a c δ t y : Nat) := disjunctionCode
  (((List.range (thresholdCode a c δ)).filter (fun j => decide (shiftedNormCode a δ ≤ j))).map fun j =>
    andCode (eqCode t (numeralCode j)) (eqCode y (numeralCode (prefixValueCode a δ j))))

def tailCode (n a c δ q t y : Nat) :=
  andCode (leCode (numeralCode (thresholdCode a c δ)) t)
    (existsCode (existsCode (conjunctionCode [
      phiChainCode δ (liftCode 2 t) (addCode (numeralCode (rayBaseCode a c)) (variableCode 1)),
      UnitArithmeticFormulaCode.unitFormulaCode q
        (variableCode 1 :: List.replicate n (numeralCode 0)) (variableCode 0),
      eqCode (liftCode 2 y) (addCode (variableCode 0) (numeralCode δ)) ])))
noncomputable def graphCode (n a c δ q t y : Nat) :=
  orCode (finitePrefixCode a c δ t y) (tailCode n a c δ q t y)

/-- Actual K ground-capture closure, fresh ground weakening, and application
at that fresh source variable. No original B/C source is modified. -/
def raySourceCode (Γ : List Nat) (src : Nat) :=
  8*Nat.pair (ContextInsertionCode.sourceCode 0 1
    (GroundCaptureClosingCode.sourceCode Γ 0 src)) 0+5

noncomputable def constantsCode (Γ : List Nat) (src : Nat) : Option (Nat×Nat×Nat) := do
  let τ ← SyntaxCode.check Γ src
  if τ = SyntaxCode.typeCode (Ty.curriedGround 1) then
    let v ← DefaultSourceAssignment.assignmentCode Γ src
    let a ← UnitHeadCode.positiveCode (v.getD 1 0)
    let c ← UnitScalarEvaluationCode.valueCode (v.getD 0 0)
    let q ← UnitEliminationBuildCode.realizedCompileCode (0::Γ) (raySourceCode Γ src)
    pure (a,c,q)
  else none

noncomputable def compileCode (Γ : List Nat) (src δ t y : Nat) : Option Nat :=
  (constantsCode Γ src).map fun p => graphCode Γ.length p.1 p.2.1 δ p.2.2 t y
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode
