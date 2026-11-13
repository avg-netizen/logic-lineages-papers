module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksRejectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (sameAccept)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject numeralNe)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem lambdaRejected (input : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) input)))
 (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 Nonempty (Derivation body Delta (⊥ : Formula alpha)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have h2 := sameReject OriginalLambdaTraversal.rawTag (two 1) (numeral 1) (numeral 2) xs
   ht (twoValue xs) (numeralNe 1 2 (by decide))
 have hi := zeroBranchElim _ _ _ (suc z) xs h2 ho
 have h1 := sameAccept OriginalLambdaTraversal.rawTag (InternalLessThan.constantOne 1) (numeral 1) xs
   ht (InternalLessThanSupportProof.oneConstantValue xs)
 exact OriginalLambdaTraversalInternalOtherTagProof.constantZeroOneFalse xs
   (successorBranchElim _ _ _ (suc z) z xs h1 hi)
theorem applicationRejected (input : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) input)))
 (ho : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
 Nonempty (Derivation body Delta (⊥ : Formula alpha)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have h2 := sameAccept OriginalLambdaTraversal.rawTag (two 1) (numeral 2) xs ht (twoValue xs)
 exact OriginalLambdaTraversalInternalOtherTagProof.constantZeroOneFalse xs
   (successorBranchElim _ _ _ (suc z) z xs h2 ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksRejectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksRejectedProof
