module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafOtherStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel eqn eqnRelabel)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedBoundedDescentNormalizer
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem outputIsMinimum (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output minimum parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative minimum input parameter)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input)))
 (hl : Nonempty (Derivation body Delta (graph2
   (OriginalLambdaTraversalSelection.leaf (EvaluatorKeyPut.refined p H G W P).base
     (EvaluatorKeyPut.refined p H G W P).window) output input parameter))) :
 Nonempty (Derivation body Delta (eqn output minimum)) := by
 apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
 intro beta j Theta typ hj ht
 have hd' := renameInto hd j Theta hj
 have hm' := renameInto hm j Theta hj
 have ho' := renameInto hother j Theta hj
 have hl' := renameInto hl j Theta hj
 simp only [EvaluatorKeyPut.Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 rw [graph2Rename] at hm' hl'
 simp only [graph1Rename,sucRelabel,zRelabel] at ho'
 simp only [consTermRename,emptyRename] at ht
 rw [eqnRelabel]
 have hv := EvaluatorKeyOtherSelectedProof.selectedLeafAtType p H G W P (input.relabel j) (minimum.relabel j)
   typ (parameter.relabel j) hd' hm' ht ho'
 exact valueUnique _ (output.relabel j) (minimum.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hl' hv

theorem atMinima (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (left right leftOut rightOut parameter leftMinimum rightMinimum : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W left parameter)))
 (hdr : Nonempty (Derivation body Delta (EvaluatorKeyPut.Domain p H G W right parameter)))
 (ha : Nonempty (Derivation body Delta (EvaluatorKeyPut.Same p H G W left right parameter)))
 (hotL : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) left)))
 (hotR : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) right)))
 (hl : Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.leaf
   (EvaluatorKeyPut.refined p H G W P).base
   (EvaluatorKeyPut.refined p H G W P).window) leftOut left parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalLambdaTraversalSelection.leaf
   (EvaluatorKeyPut.refined p H G W P).base
   (EvaluatorKeyPut.refined p H G W P).window) rightOut right parameter)))
 (hml : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative leftMinimum left parameter)))
 (hmr : Nonempty (Derivation body Delta (graph2
   (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative rightMinimum right parameter))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 obtain ⟨hel⟩ := outputIsMinimum p H G W P left leftOut leftMinimum parameter hd hml hotL hl
 obtain ⟨her⟩ := outputIsMinimum p H G W P right rightOut rightMinimum parameter hdr hmr hotR hr
 have he := EvaluatorKeyMinimumProof.actualMinimumEquality p H G W P body alpha Delta
   left right leftMinimum rightMinimum parameter hd hdr ha hml hmr
 have heq := (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn leftMinimum rightMinimum)).mp he
 obtain ⟨heq⟩ := heq
 have hresult : Nonempty (Derivation body Delta (eqn leftOut rightOut)) :=
   ⟨InternalTagArithmeticSupportProof.trans hel (InternalTagArithmeticSupportProof.trans heq (InternalTagArithmeticSupportProof.symm her))⟩
 exact (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn leftOut rightOut)).mpr hresult

theorem actualOtherLeafEquality : EvaluatorKeyOtherLeafTargets.ActualOtherLeafEquality := by
 intro p H G W P body alpha Delta left right leftOut rightOut parameter
 dsimp only
 intro hd hdr ha hotL hotR hl hr
 let Min := (EvaluatorKeyPut.minimumInputs p H G W P).base.oldRepresentative
 let qs : Fin 2 → Program 3 := ![.composition Min ![.projection 0,.projection 2],.composition Min ![.projection 1,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := ![left,right,parameter]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta values hj hg
 let xx : Fin 3 → OTerm beta := ![left.relabel j,right.relabel j,parameter.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 have hd' := renameInto hd j Theta hj
 have hdr' := renameInto hdr j Theta hj
 have ha' := renameInto ha j Theta hj
 have hotL' := renameInto hotL j Theta hj
 have hotR' := renameInto hotR j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 simp only [EvaluatorKeyPut.Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 simp only [EvaluatorKeyPut.Domain,OriginalActiveKernelMinimumSupportProof.domainRename] at hdr'
 simp only [EvaluatorKeyPut.Same, SixSol20261113.Erasure.EvaluatorErasureSyntax.sameRename] at ha'
 simp only [graph1Rename,InternalOriginalStepGuardSupportProof.oneRename] at hotL' hotR'
 rw [graph2Rename] at hl' hr'
 rw [equalEqn,eqnRelabel]
 rw [← equalEqn]
 have hml := binaryRecover Min (.projection 0) (.projection 2) (values 0) (left.relabel j) (parameter.relabel j)
   xx (hg 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have hmr := binaryRecover Min (.projection 1) (.projection 2) (values 1) (right.relabel j) (parameter.relabel j)
   xx (hg 1) (projectionValue 1 xx) (projectionValue 2 xx)
 exact atMinima p H G W P (left.relabel j) (right.relabel j) (leftOut.relabel j) (rightOut.relabel j)
   (parameter.relabel j) (values 0) (values 1) hd' hdr' ha' hotL' hotR' hl' hr' hml hmr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherLeafProof
