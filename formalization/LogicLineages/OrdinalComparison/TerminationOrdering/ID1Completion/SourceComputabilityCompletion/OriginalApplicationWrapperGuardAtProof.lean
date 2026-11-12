module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open OriginalTransparentMixedPathInternalDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atEdges (source : Program 2) (endpoint : Program 6)
 (s t cert parameter childS childT childCert arg d e arrow childEdge parentEdge : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)))
 (hc : Nonempty (Derivation body Delta (graph3 edgeCode childEdge childS childT childCert)))
 (hp : Nonempty (Derivation body Delta (graph3 edgeCode parentEdge s t cert)))
 (hend : Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph endpoint (suc z) d e childS childT arg parameter))) :
 Nonempty (Derivation body Delta (graph4 (OriginalNeutralLeaf.guardAt endpoint) (suc z) s t cert parameter)) := by
 have hs := andLeft hh
 have hsa := andLeft (andRight hh)
 have hta := andLeft (andRight (andRight hh))
 have har := andLeft (andRight (andRight (andRight hh)))
 have hst := andLeft (andRight (andRight (andRight (andRight hh))))
 have htt := andLeft (andRight (andRight (andRight (andRight (andRight hh)))))
 have hat := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hstep := andRight (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have htagged : Nonempty (Derivation body Delta (InternalApplicationStepPeel.taggedEdge d e arrow childS childT arg childEdge childCert)) :=
   andIntro har (andIntro hst (andIntro htt (andIntro hat hc)))
 have hlift := edgeLiftBackward d e arg childEdge childS childT childCert s t cert parentEdge
   (andIntro hc (andIntro hsa (andIntro hta hstep))) hp
 have hg := OriginalApplicationWrapperEndpointProof.guardValue endpoint d e arrow childS childT arg childEdge childCert parentEdge parameter htagged hend hlift
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have he : Nonempty (Derivation body Delta (programGraph OriginalTransparentApplicationFunctionDefinitions.edge parentEdge xs)) := by
   apply compositionValue edgeCode ![.projection 0,.projection 1,.projection 2] parentEdge xs
     (Fin.cons s (Fin.cons t (Fin.cons cert Fin.elim0))) hp
   intro i
   exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
     (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k))) i
 exact binaryValue (InternalParameterizedApplicationStepChecker.guardP endpoint)
  InternalParameterizedApplicationStepChecker.edgeStateP (.projection 3) (suc z) parentEdge parameter xs
  hg he (projectionValue 3 xs)

theorem guardAt (source : Program 2) (endpoint : Program 6)
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)))
 (hend : Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph endpoint (suc z) d e childS childT arg parameter))) :
 Nonempty (Derivation body Delta (graph4 (OriginalNeutralLeaf.guardAt endpoint) (suc z) s t cert parameter)) := by
 apply programCases edgeCode (Fin.cons childS (Fin.cons childT (Fin.cons childCert Fin.elim0))) _
 intro beta j Theta childEdge hj hc
 simp only [graph4Rename,sucRelabel,zRelabel]
 have hend' := renameInto hend j Theta hj
 simp only [InternalParameterizedApplicationStepCheckerSyntaxProof.endpointGraphRename,sucRelabel,zRelabel] at hend'
 have hh' := renameInto hh j Theta hj
 simp only [ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
   OriginalLambdaConstructorGraphSyntaxProof.oneRename] at hh'
 simp only [consTermRename,emptyRename] at hc
 apply programCases edgeCode (Fin.cons (s.relabel j) (Fin.cons (t.relabel j) (Fin.cons (cert.relabel j) Fin.elim0))) _
 intro gamma k Xi parentEdge hk hp
 simp only [conjunctionRename,graph1Rename,graph4Rename,sucRelabel,zRelabel]
 have hend'' := renameInto hend' k Xi hk
 simp only [InternalParameterizedApplicationStepCheckerSyntaxProof.endpointGraphRename,sucRelabel,zRelabel] at hend''
 have hh'' := renameInto hh' k Xi hk
 simp only [ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
   OriginalLambdaConstructorGraphSyntaxProof.oneRename] at hh''
 have hc' := renameInto hc k Xi hk
 simp only [programRename,consTermRename,emptyRename] at hc'
 simp only [consTermRename,emptyRename] at hp
 exact atEdges source endpoint ((s.relabel j).relabel k) ((t.relabel j).relabel k)
   ((cert.relabel j).relabel k) ((parameter.relabel j).relabel k)
   ((childS.relabel j).relabel k) ((childT.relabel j).relabel k) ((childCert.relabel j).relabel k)
   ((arg.relabel j).relabel k) ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((arrow.relabel j).relabel k)
   (childEdge.relabel k) parentEdge hh'' hc' hp hend''

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardAtProof
