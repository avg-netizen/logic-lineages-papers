module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open OriginalLambdaGuardLeaf
open OriginalHereditaryLambdaChildBranchProof (activeRename)
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atType (source : Program 2) (leaf : Program 4) (s t cert parameter typ : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (graph4 (OriginalLambdaDirectBottomTrace.hop source leaf) (suc z) s t cert parameter)))
 (htype : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s))) :
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) s ⊓
 OriginalHereditaryLambda.LambdaNonbottom s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have hguard := andLeft (conjunctionRecover (OriginalTransparentLambdaStep.hopGuard source) leaf xs hh)
 have hlambda := andRight (conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs hguard)
 have hs := andLeft (conjunctionRecover sourceLambda _ xs hlambda)
 have hrest := andRight (conjunctionRecover sourceLambda _ xs hlambda)
 have hm := andLeft (conjunctionRecover matchingTarget OriginalHereditaryLambda.lamPath xs hrest)
 have ht := andLeft (conjunctionRecover targetLambda _ xs hm)
 have hsTest := unaryRecover lambdaTest (.projection 0) (suc z) s xs hs (projectionValue 0 xs)
 have htTest := unaryRecover lambdaTest (.projection 1) (suc z) t xs ht (projectionValue 1 xs)
 have hsTag := sameRightRecover OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
   (suc z) (Fin.cons s Fin.elim0) hsTest (InternalLessThanSupportProof.oneConstantValue _)
 have htTag := sameRightRecover OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
   (suc z) (Fin.cons t Fin.elim0) htTest (InternalLessThanSupportProof.oneConstantValue _)
 have hn := OriginalTransparentLambdaStepHereditaryControlProof.sameBottomReject s t cert parameter typ htype htTag
 have hz := OriginalTransparentLambdaValidityInternalBooleanProof.sameReject
   (.projection 1) OriginalConstructorLeaf.expectedBottom xs hn
 exact andIntro hsTag (andIntro hs hz)

theorem hopConditions (source : Program 2) (leaf : Program 4) (s t cert parameter : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (graph4 (OriginalLambdaDirectBottomTrace.hop source leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) s ⊓
 OriginalHereditaryLambda.LambdaNonbottom s t cert parameter)) := by
 apply programCases InternalUnpair.left (Fin.cons s Fin.elim0) _
 intro beta j Theta typ hj ht
 have hh' := renameInto hh j Theta hj
 simp only [graph4Rename,sucRelabel,zRelabel] at hh'
 simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph1Rename,sucRelabel,zRelabel,activeRename]
 simp only [consTermRename,emptyRename] at ht
 exact atType source leaf (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) typ hh' ht

theorem actualHopConditions : OriginalLambdaDirectBottomTraceHopTargets.ActualHopConditions := by
 intro source leaf body alpha Delta s t cert parameter hh
 exact hopConditions source leaf s t cert parameter hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceHopProof
