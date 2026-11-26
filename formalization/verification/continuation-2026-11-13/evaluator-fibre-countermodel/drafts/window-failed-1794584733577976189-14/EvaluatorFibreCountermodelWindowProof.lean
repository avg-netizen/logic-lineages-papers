module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelWindowProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedFiniteUniverse
open EvaluatorFibreCountermodel
theorem actualWindow : EvaluatorFibreCountermodelTargets.ActualWindow := by
 refine ⟨Encodable.encodek context,?_,?_,?_,?_,?_⟩
 · intro sigma hs tau ht
   simp only [context,List.mem_singleton] at hs
   subst sigma
   simpa only [Ty.subtypes,List.mem_singleton] using ht
 · simp [HeadInWindow,RankedCovered,context,arity,headArguments,headResult]
 · simp [HeadInWindow,RankedCovered,context,headArguments,headResult]
 · simp [leftTerm,leftBase,bottom,zero,InUniverse,auxTypesAllowed,auxArgumentTypesAllowed,
     auxHeadsAllowed,auxArgumentsAllowed,HeadInWindow,RankedCovered,context,arity,headArguments,headResult]
 · simp [rightTerm,rightBase,bottom,zero,InUniverse,auxTypesAllowed,auxArgumentTypesAllowed,
     auxHeadsAllowed,auxArgumentsAllowed,HeadInWindow,RankedCovered,context,arity,headArguments,headResult]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelWindowProof
