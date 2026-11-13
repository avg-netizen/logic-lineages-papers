module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidityInternalNodeSupportProof (equalityCases weakenProof)
open OriginalLambdaTraversalInternalOtherTagProof (constantZeroOneFalse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Literal OTHER predicate depends only on its actual raw-tag output. -/
theorem atTag (left right tag : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (graph1 rawTag tag left)))
 (hr : Nonempty (Derivation body Delta (graph1 rawTag tag right)))
 (ho : Nonempty (Derivation body Delta (graph1 otherTag (suc z) left))) :
 Nonempty (Derivation body Delta (graph1 otherTag (suc z) right)) := by
 let ls : Fin 1 → OTerm alpha := Fin.cons left Fin.elim0
 let rs : Fin 1 → OTerm alpha := Fin.cons right Fin.elim0
 apply equalityCases tag (numeral 2) _
 · intro Xi inc h2
   have lc := binaryValue InternalEqualityTest.equalityTest rawTag (two 1) z tag (numeral 2) ls
     h2 (weakenProof hl inc) (twoValue ls)
   have rc := binaryValue InternalEqualityTest.equalityTest rawTag (two 1) z tag (numeral 2) rs
     h2 (weakenProof hr inc) (twoValue rs)
   have hi := zeroBranchElim _ _ _ (suc z) ls lc (weakenProof ho inc)
   apply equalityCases tag (suc z) _
   · intro Omega inc2 h1
     have r1 := binaryValue InternalEqualityTest.equalityTest rawTag (InternalLessThan.constantOne 1)
       z tag (suc z) rs h1 (weakenProof hr (fun f hf => inc2 f (inc f hf)))
       (InternalLessThanSupportProof.oneConstantValue rs)
     exact zeroBranchIntro _ _ _ (suc z) rs (weakenProof rc inc2)
       (zeroBranchIntro _ _ _ (suc z) rs r1 (InternalLessThanSupportProof.oneConstantValue rs))
   · intro Omega inc2 h1
     have l1 := binaryValue InternalEqualityTest.equalityTest rawTag (InternalLessThan.constantOne 1)
       (suc z) tag (suc z) ls h1 (weakenProof hl (fun f hf => inc2 f (inc f hf)))
       (InternalLessThanSupportProof.oneConstantValue ls)
     obtain ⟨hf⟩ := constantZeroOneFalse ls
       (successorBranchElim _ _ _ (suc z) z ls l1 (weakenProof hi inc2))
     exact ⟨Derivation.explosion hf⟩
 · intro Xi inc h2
   have lc := binaryValue InternalEqualityTest.equalityTest rawTag (two 1) (suc z) tag (numeral 2) ls
     h2 (weakenProof hl inc) (twoValue ls)
   obtain ⟨hf⟩ := constantZeroOneFalse ls
     (successorBranchElim _ _ _ (suc z) z ls lc (weakenProof ho inc))
   exact ⟨Derivation.explosion hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherTagProof
