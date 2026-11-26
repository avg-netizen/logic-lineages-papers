module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
/-- All actual typed inputs, arbitrary R and original window code c. -/
def NativeCalibration : Prop := ∀ R n arity c (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
 evaluate (OriginalHereditaryEvaluatorDefinitions.evaluator R) (List.Vector.ofFn ![
   packedNumber q, Nat.pair c (typesNumber Gamma)]) =
 OriginalHereditarySettledObserverDefinitions.settledValue R c ⟨Gamma,q⟩
/-- Original source-domain invariance, not an internal derivability law. -/
def SourcePreserves : Prop := ∀ R n arity symbols S c,
 SubtypeClosed (fun t => t ∈ S) →
 OriginalHereditaryObservationSourceUniformityTargets.SourceUniform R n arity symbols S c →
 OriginalHereditaryObservationSourceUniformityTargets.SourceUniform
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) n arity symbols S c

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorTargets
