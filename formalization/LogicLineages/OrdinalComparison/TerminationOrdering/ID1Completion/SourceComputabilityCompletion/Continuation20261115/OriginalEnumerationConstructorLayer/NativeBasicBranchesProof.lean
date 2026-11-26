module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeBranchesProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedCodeEnumerationPrimrecSupportProof (cross)
open NativeSupportProof
open OriginalRawSyntaxTransportConstructorEvaluationProof

def inputs {n : Nat} (types : List Source.Ty) (heads : List (HeadCode (Fin n)))
    (labels tupleBound variableBound : Nat) (prior opened : List (Code (Fin n))) : List.Vector Nat 7 :=
  ofFn ![Encodable.encode types,Encodable.encode heads,labels,tupleBound,variableBound,
    Encodable.encode prior,Encodable.encode opened]
variable (n : Nat) (types : List Source.Ty) (heads : List (HeadCode (Fin n)))
    (labels tupleBound variableBound : Nat) (prior opened : List (Code (Fin n)))

theorem variablesValue : evaluate variableBranch (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode ((List.range variableBound).map (Code.var : Nat → Code (Fin n))) := by
  change evaluate (InternalListMap.map OriginalRawSyntaxTransport.variableConstructor)
    (ofFn ![evaluate OriginalAscendingRange.range (ofFn ![variableBound])]) = _
  rw [OriginalAscendingRange.NativeProof.nativeRange]
  apply mapEncoding
  intro i
  rw [variableConstructorEvaluation]
  simp only [Encodable.encode_nat]
  rfl

theorem lambdaPairsValue : evaluate lambdaPairs (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode (cross types opened) := by
  change evaluate NumericDependencyCross.cross (ofFn ![Encodable.encode types,Encodable.encode opened]) = _
  exact crossEncoding types opened

theorem lambdasValue : evaluate lambdas (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode ((cross types opened).map (fun q => Code.lam q.1 q.2)) := by
  change evaluate (InternalListMap.map (tagPayload 1))
    (ofFn ![evaluate lambdaPairs (inputs types heads labels tupleBound variableBound prior opened)]) = _
  rw [lambdaPairsValue]
  apply mapEncoding
  intro q
  rw [tagValue]
  change Nat.pair 1 (Encodable.encode q) = _
  rcases q with ⟨t,c⟩
  simp only [Encodable.encode_prod_val,OriginalContextExtensionCalibrationProof.typeEncoding]
  rfl

theorem childPairsValue : evaluate childPairs (inputs types heads labels tupleBound variableBound prior opened) =
    Encodable.encode (cross prior prior) := by
  change evaluate NumericDependencyCross.cross (ofFn ![Encodable.encode prior,Encodable.encode prior]) = _
  exact crossEncoding prior prior

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeBranchesProof
