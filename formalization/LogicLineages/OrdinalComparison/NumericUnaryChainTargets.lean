module
public import LogicLineages.OrdinalComparison.NumericUnaryChainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Targets
open HeterogeneousUnaryAssembly ScalarCarrierAccounting OriginalDomain

def ExactMergedPayloads : Prop := ∀ (Γ : List Ty) (ops : List (Operator Γ)),
  contextCode (Γ.map SyntaxCode.typeCode) (ops.map operatorCode) = (context ops).map SyntaxCode.typeCode ∧
  (mergeData (ops.map operatorCode)).1 = (ops.map (fun op => op.privateContext.length)).sum ∧
  (mergeData (ops.map operatorCode)).2 = (merged ops).map pairCode

def ExactSingleLambda : Prop := ∀ (Γ : List Ty) (vs : List (OriginalTerm Γ (Ty.curriedGround 1))),
  bodyCode (vs.map SyntaxCode.encodeTerm) = SyntaxCode.encodeTerm (SourceUnaryChain.chainBody vs) ∧
  chainCode (vs.map SyntaxCode.encodeTerm) = SyntaxCode.encodeTerm (SourceUnaryChain.chainSource vs)

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec₂ contextCode ∧ Primrec mergeData ∧ Primrec chainCode ∧ Primrec₂ compileCode

/-- Given actual heterogeneous inputs, the compiler constructs the literal
merged one-lambda source and its entire actual vector, with the exact head sum.
No source extraction or arbitrary private-value identification is assumed. -/
def ActualCompiledChain : Prop := ∀ (Γ : List Ty) (ops : List (Operator Γ)),
  ∃ v : OrdinalVector (context ops) 1,
    compileCode (Γ.map SyntaxCode.typeCode) (ops.map operatorCode) =
      some ((context ops).map SyntaxCode.typeCode,
        SyntaxCode.encodeTerm (SourceUnaryChain.chainSource (terms ops)),OrdinalSyntax.vectorCode v) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (SourceUnaryChain.chainSource (terms ops)) = some v ∧
    ∀ μ : Variable (context ops) .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (v 1) =
        chargedSum (ops.map (fun op => unitValue (op.vector 1)))
end LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Targets
