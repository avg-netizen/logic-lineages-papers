module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInversePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalApplicationValidityClosure (applicationConstructors)
open OriginalTransparentApplicationFunctionDefinitions
open OriginalTransparentMixedPathInternalDefinitions (ApplicationHop)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualInverse : OriginalTransparentApplicationFunctionInverseTargets.ActualInverse := by
 intro S body alpha Delta s t cert parameter arrow d e fp ap fn arg targetFn childCert hc hg htf hck
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 apply programCases edge xs _
 intro beta j Theta state hj hedge
 simp only [xs,consTermRename,emptyRename] at hedge
 let xx : Fin 4 → OTerm beta := Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
   (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
 have hc' := renameInto hc j Theta hj
 simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
 have hg' := renameInto hg j Theta hj
 have htf' := renameInto htf j Theta hj
 have hck' := renameInto hck j Theta hj
 simp only [graph4Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel] at hg' htf' hck'
 simp only [ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
   SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel]
 have hparts := conjunctionRecover (OriginalTransparentVariableStep.sourceAt S) structuralGuard xx hg'
 have hsource := binaryRecover S (.projection 0) (.projection 3) (suc z)
   (s.relabel j) (parameter.relabel j) xx (andLeft hparts) (projectionValue 0 xx) (projectionValue 3 xx)
 have hstruct := unaryRecover InternalApplicationStepPeel.structuralGuard edge (suc z) state xx (andRight hparts) hedge
 have htfn := unaryRecover InternalApplicationStepPeel.targetFunctionCode edge (targetFn.relabel j) state xx htf' hedge
 have hk := unaryRecover InternalApplicationStepPeel.peeledStep edge (childCert.relabel j) state xx hck' hedge
 have hedge3 : Nonempty (Derivation body Theta (graph3 edgeCode state (s.relabel j) (t.relabel j) (cert.relabel j))) := by
   apply compositionRecover edgeCode ![.projection 0,.projection 1,.projection 2] state xx
     (Fin.cons (s.relabel j) (Fin.cons (t.relabel j) (Fin.cons (cert.relabel j) Fin.elim0))) hedge
   intro i
   exact Fin.cases (projectionValue 0 xx) (Fin.cases (projectionValue 1 xx)
     (Fin.cases (projectionValue 2 xx) (fun k => Fin.elim0 k))) i
 have selectors := edgeSelectors state (s.relabel j) (t.relabel j) (cert.relabel j) hedge3
 have htgt := OriginalTransparentApplicationFunctionInverseGeometryProof.targetAtState state (s.relabel j) (t.relabel j)
   (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
   (fn.relabel j) (arg.relabel j) (targetFn.relabel j) hc'
   (andLeft selectors) (andLeft (andRight selectors)) hstruct htfn
 have hprefix := OriginalTransparentApplicationFunctionInversePrefixProof.recoverPrefix state (cert.relabel j) (childCert.relabel j)
   hstruct (andRight (andRight selectors)) hk
 have hfn := andLeft (andRight hc')
 have harg := andLeft (andRight (andRight hc'))
 have happ := applicationBackward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
   (fp.relabel j) (ap.relabel j) (s.relabel j) (pairRight _ _ _ hfn) (pairRight _ _ _ harg)
   (andRight (andRight (andRight hc')))
 exact andIntro hsource (andIntro happ (andIntro (andLeft htgt) (andIntro (andLeft hc')
   (andIntro (pairLeft _ _ _ hfn) (andIntro (andRight htgt) (andIntro (pairLeft _ _ _ harg) hprefix))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionInverseProof
