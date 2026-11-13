module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationTraceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace OriginalMixedClosedTraceInductionDefinitions
open GuardedErasureFinalGraphsProof GuardedErasurePackingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Original application inverse, exact path-tail descent and raw erasure
queries are reused. The internally discharged child row now retains C∧W. -/
theorem atFields (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  fn arg domain codomain arrow fp ap childT childCert next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (literalSource p H G W)
   (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (literalSource p H G W)
   (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hsf : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap fn arg s)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard (literalSource p H G W)) (suc z) s t cert oldParam)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.targetFunction childT s t cert oldParam)))
 (hk : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (literalSource p H G W)
   (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W))
   s t newParam erasedS erasedT)) := by
 have hp := andLeft hf
 have hsrc := andLeft (andRight hf)
 have hleaf := andLeft (andRight (andRight hf))
 have ha := andLeft (andRight (andRight (andRight hf)))
 have hin := andLeft (andRight (andRight (andRight (andRight hf))))
 have hop := andLeft (andRight (andRight (andRight (andRight (andRight hf)))))
 have hnp := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf))))))
 have hes := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))
 have het := andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))
 have hh := OriginalTransparentApplicationFunctionInverseProof.actualInverse (literalSource p H G W)
  body alpha Delta s t cert oldParam arrow domain codomain fp ap fn arg childT childCert hsf hguard ht hk
 have hlinks := OriginalTransparentMixedPathApplicationFieldsProof.applicationFields
  (literalSource p H G W) s t cert oldParam fn childT childCert arg domain codomain arrow hh
 have hstep := andRight (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hs := andLeft (andRight (andRight hlinks))
 have hknown := OriginalMixedDirectBottomTraceApplicationRecognitionProof.applicationChild
  (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
  s t cert oldParam path head tail fn childT childCert next out hp hc hstep hs ht hk hlive hrun hfinish
 have ih := OriginalMixedClosedTraceApplicationChildProof.contextIH _ _ (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) path head tail
  fn childT childCert oldParam d cutoff c hi hc (andLeft hknown) (andRight hknown)
 have hr := GuardedErasureApplicationErasureProof.atFields p H G W P body alpha Delta
  s t cert oldParam fn childT childCert arg domain codomain arrow fp ap erasedS erasedT newParam
  d cutoff gamma extended c hsf hh hleaf (andRight hknown) hin hop hnp hes het ih
 have he := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G (member p) W
  s erasedS d cutoff gamma extended c oldParam newParam hin hes hop hnp hsrc
 exact andIntro he hr

theorem queryFields (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  fn arg domain codomain arrow fp ap next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (literalSource p H G W)
   (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (literalSource p H G W)
   (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hsf : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap fn arg s)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard (literalSource p H G W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (literalSource p H G W)
   (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W))
   s t newParam erasedS erasedT)) := by
 let qs : Fin 2 → Program 4 := ![OriginalTransparentApplicationFunctionDefinitions.targetFunction,
   OriginalTransparentApplicationFunctionDefinitions.childCertificate]
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons oldParam Fin.elim0)))
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [xs,consTermRename,emptyRename] at hq
 have hi' := renameInto hi j Theta hj
 have hc' := renameInto hc j Theta hj
 have hf' := renameInto hf j Theta hj
 have hsf' := renameInto hsf j Theta hj
 have hg' := renameInto hguard j Theta hj
 have hl' := renameInto hlive j Theta hj
 have hr' := renameInto hrun j Theta hj
 have hz' := renameInto hfinish j Theta hj
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [InternalApplicationValidityClosure.applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hsf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedClosedTraceInductionSyntaxProof.resultRename]
 exact atFields p H G W P
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
  (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j)
  (fn.relabel j) (arg.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j) (fp.relabel j) (ap.relabel j)
  (ys 0) (ys 1) (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf' hg' (hq 0) (hq 1) hl' hr' hz'

theorem applicationBranch (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
  next out : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (literalSource p H G W)
   (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep) (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (literalSource p H G W)
   (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
   path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)))
 (hguard : Nonempty (Derivation body Delta (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard (literalSource p H G W)) (suc z) s t cert oldParam)))
 (hlive : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert oldParam)))
 (hrun : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph
  (transition (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) out tail next)))
 (hfinish : Nonempty (Derivation body Delta (graph1
  (finish (literalSource p H G W) (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)) (suc z) out))) :
 Nonempty (Derivation body Delta (result (literalSource p H G W)
   (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W))
   s t newParam erasedS erasedT)) := by
 have htag := OriginalTransparentApplicationFunctionInverseTagProof.sourceTag
  (literalSource p H G W) s t cert oldParam hguard
 apply OriginalPackedSourceApplicationFieldsProof.actualFieldsCases body alpha Delta H G (member p) W s oldParam _
  (andLeft (andRight hf)) htag
 intro beta j Theta arrow domain codomain fp ap fn arg incl hsf hfn harg
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hf' := renameInto hf j Theta incl
 have hg' := renameInto hguard j Theta incl
 have hl' := renameInto hlive j Theta incl
 have hr' := renameInto hrun j Theta incl
 have hz' := renameInto hfinish j Theta incl
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.fieldsRename] at hf'
 simp only [graph4Rename,sucRelabel,zRelabel] at hg' hl'
 simp only [InternalRawListRepeatSyntaxProof.repeatRename] at hr'
 simp only [graph1Rename,sucRelabel,zRelabel] at hz'
 rw [OriginalMixedClosedTraceInductionSyntaxProof.resultRename]
 exact queryFields p H G W P
  (path.relabel j) (head.relabel j) (tail.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j)
  (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
  (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j)
  fn arg domain codomain arrow fp ap (next.relabel j) (out.relabel j)
  hi' hc' hf' hsf hg' hl' hr' hz'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationTraceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationTraceProof
