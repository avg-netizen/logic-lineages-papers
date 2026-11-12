module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationFieldsProof
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

def Fields {alpha : Type} (source : Program 2)
 (s t cert parameter childS childT childCert : OTerm alpha) : Formula alpha :=
 graph1 OriginalLambdaTraversal.rawTag (suc (suc z)) s ⊓
 (graph4 (OriginalTransparentApplicationFunctionDefinitions.hopGuard source) (suc z) s t cert parameter ⊓
 (graph4 OriginalTransparentApplicationFunctionDefinitions.sourceFunction childS s t cert parameter ⊓
 (graph4 OriginalTransparentApplicationFunctionDefinitions.targetFunction childT s t cert parameter ⊓
 graph4 OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert parameter)))

theorem atEdges (source : Program 2)
 (s t cert parameter childS childT childCert arg d e arrow childEdge parentEdge : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)))
 (hc : Nonempty (Derivation body Delta (graph3 edgeCode childEdge childS childT childCert)))
 (hp : Nonempty (Derivation body Delta (graph3 edgeCode parentEdge s t cert))) :
 Nonempty (Derivation body Delta (Fields source s t cert parameter childS childT childCert)) := by
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
 have fields := OriginalTransparentApplicationFunctionPeelFieldsProof.actualFields body alpha Delta
   d e arrow childS childT arg childEdge childCert parentEdge htagged hlift
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have he : Nonempty (Derivation body Delta (programGraph OriginalTransparentApplicationFunctionDefinitions.edge parentEdge xs)) := by
   apply compositionValue edgeCode ![.projection 0,.projection 1,.projection 2] parentEdge xs
     (Fin.cons s (Fin.cons t (Fin.cons cert Fin.elim0))) hp
   intro i
   exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
     (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k))) i
 have hguard := unaryValue InternalApplicationStepPeel.structuralGuard
   OriginalTransparentApplicationFunctionDefinitions.edge (suc z) parentEdge xs (andLeft fields) he
 have hsource : Nonempty (Derivation body Delta
   (programGraph (OriginalTransparentVariableStep.sourceAt source) (suc z) xs)) :=
   binaryValue source (.projection 0) (.projection 3) (suc z) s parameter xs hs
     (projectionValue 0 xs) (projectionValue 3 xs)
 have hhop := conjunctionAccept (OriginalTransparentVariableStep.sourceAt source)
   OriginalTransparentApplicationFunctionDefinitions.structuralGuard xs hsource hguard
 have hf := unaryValue InternalApplicationStepPeel.functionCode
   OriginalTransparentApplicationFunctionDefinitions.edge childS parentEdge xs (andLeft (andRight fields)) he
 have ht := unaryValue InternalApplicationStepPeel.targetFunctionCode
   OriginalTransparentApplicationFunctionDefinitions.edge childT parentEdge xs (andLeft (andRight (andRight fields))) he
 have hk := unaryValue InternalApplicationStepPeel.peeledStep
   OriginalTransparentApplicationFunctionDefinitions.edge childCert parentEdge xs (andRight (andRight (andRight fields))) he
 have htag := andLeft (OriginalLambdaTraversalApplicationFieldsProof.fromRaw arrow d e childS arg s har hst hat hsa)
 exact andIntro htag (andIntro hhop (andIntro hf (andIntro ht hk)))

theorem applicationFields (source : Program 2)
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow))) :
 Nonempty (Derivation body Delta (Fields source s t cert parameter childS childT childCert)) := by
 apply programCases edgeCode (Fin.cons childS (Fin.cons childT (Fin.cons childCert Fin.elim0))) _
 intro beta j Theta childEdge hj hc
 simp only [Fields,conjunctionRename,graph1Rename,graph4Rename,sucRelabel,zRelabel]
 have hh' := renameInto hh j Theta hj
 simp only [ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
   OriginalLambdaConstructorGraphSyntaxProof.oneRename] at hh'
 simp only [consTermRename,emptyRename] at hc
 apply programCases edgeCode (Fin.cons (s.relabel j) (Fin.cons (t.relabel j) (Fin.cons (cert.relabel j) Fin.elim0))) _
 intro gamma k Xi parentEdge hk hp
 simp only [conjunctionRename,graph1Rename,graph4Rename,sucRelabel,zRelabel]
 have hh'' := renameInto hh' k Xi hk
 simp only [ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
   OriginalLambdaConstructorGraphSyntaxProof.oneRename] at hh''
 have hc' := renameInto hc k Xi hk
 simp only [programRename,consTermRename,emptyRename] at hc'
 simp only [consTermRename,emptyRename] at hp
 exact atEdges source ((s.relabel j).relabel k) ((t.relabel j).relabel k)
   ((cert.relabel j).relabel k) ((parameter.relabel j).relabel k)
   ((childS.relabel j).relabel k) ((childT.relabel j).relabel k) ((childCert.relabel j).relabel k)
   ((arg.relabel j).relabel k) ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((arrow.relabel j).relabel k)
   (childEdge.relabel k) parentEdge hh'' hc' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationFieldsProof
