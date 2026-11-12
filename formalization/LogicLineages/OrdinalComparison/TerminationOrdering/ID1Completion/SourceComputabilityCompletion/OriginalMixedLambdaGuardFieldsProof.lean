module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (z suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem bodyType (parent child typ : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.bodyCode child typ parent))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ child)) := by
 apply programCases OriginalLambdaConstructor.bodyPayload (Fin.cons parent Fin.elim0) _
 intro beta j Theta payload hj hp
 rw [graph1Rename]
 simp only [consTermRename,emptyRename] at hp
 have hb' := renameInto hb j Theta hj
 rw [graph2Rename] at hb'
 exact pairLeft (child.relabel j) (typ.relabel j) payload
  (OriginalLambdaConstructorGraphSupportProof.bodyCodeRecover (child.relabel j) (typ.relabel j) (parent.relabel j) payload hb' hp)

theorem actualAtFields : OriginalMixedLambdaGuardFieldsTargets.ActualAtFields := by
 intro source body alpha Delta s t cert parameter childS childT childCert childParam d e arrow context gamma extended hsf hg htarget hcert hparameter hp he
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hg1 := conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) _ xs hg
 have hg2 := conjunctionRecover OriginalLambdaGuardLeaf.sourceLambda _ xs (andRight hg1)
 have hg3 := conjunctionRecover OriginalLambdaGuardLeaf.matchingTarget OriginalHereditaryLambda.lamPath xs (andRight hg2)
 have hs := binaryRecover source (.projection 0) (.projection 3) (suc z) s parameter xs
  (andLeft hg1) (projectionValue 0 xs) (projectionValue 3 xs)
 have htf := OriginalLambdaRecoveredGeometryProof.targetFields s t cert parameter childS childT d e arrow hsf (andLeft hg3) htarget
 have hprefix := OriginalHereditaryLambdaPrefixProof.recoverPrefix xs childCert (andRight hg3) hcert
 have hcp := OriginalLambdaRecoveredGeometryProof.parameterAtExtension s t cert parameter childS childParam d e arrow context gamma extended hsf hp he hparameter
 have hcs := OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction s d e childS arrow hsf
 have hct := OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction t d e childT arrow htf
 have hts := bodyType s childS e (andRight (andRight (andRight (andRight hsf))))
 have htt := bodyType t childT e (andRight (andRight (andRight (andRight htf))))
 exact andIntro htf (andIntro hs (andIntro hcs (andIntro hct (andIntro hts (andIntro htt
  (andIntro hprefix (andIntro hp (andIntro he hcp))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsProof
