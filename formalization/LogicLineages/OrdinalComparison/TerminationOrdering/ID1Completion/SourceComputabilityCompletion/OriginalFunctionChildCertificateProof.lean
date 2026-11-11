module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateCodesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open OriginalFunctionChildCertificate OriginalFunctionChildCertificateTargets

/-- Both source-witness code constructors are internally total ORIGINAL
Programs. Their graph equations, the unchanged child edge and the original
Object source certificate remain together in the exact continuation. -/
theorem actualOriginalFinalFunctionChildCertificate : ActualOriginalFinalFunctionChildCertificate := by
  intro p
  dsimp only
  intro context alpha Gamma sigma tau F A X gammaCode function argument out parameter targetFunction vertex G V child psi
    hrec he next
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let data := OuterSelection.data r.base r.window
  apply programCases InternalPairing.pairing (Fin.cons targetFunction (Fin.cons child Fin.elim0)) psi
  intro beta j Delta entry hj hp
  have hp' : Nonempty (Derivation (SourcePresentation.sourceBody (GlobalSourcePackage.source r) context) Delta
      (graph2 InternalPairing.pairing entry (targetFunction.relabel j) (child.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using hp
  have hrec' := renameInto hrec j Delta hj
  rw [OriginalSourceApplicationReconstructionSyntaxProof.recoveredRename] at hrec'
  have he' := renameInto he j Delta hj
  rw [edgeRename] at he'
  apply programCases InternalListCodec.consCode (Fin.cons entry (Fin.cons z Fin.elim0)) (psi.relabel j)
  intro gamma k Theta pathCode hk hc
  have hc' : Nonempty (Derivation (SourcePresentation.sourceBody (GlobalSourcePackage.source r) context) Theta
      (graph2 InternalListCodec.consCode pathCode (entry.relabel k) z)) := by
    simpa only [graph2,consTermRename,emptyRename,zRelabel] using hc
  have hp'' := renameInto hp' k Theta hk
  rw [graph2Rename] at hp''
  have hrec'' := renameInto hrec' k Theta hk
  rw [OriginalSourceApplicationReconstructionSyntaxProof.recoveredRename] at hrec''
  have he'' := renameInto he' k Theta hk
  rw [edgeRename] at he''
  have result := OriginalFunctionChildCertificateCodesProof.atCodes p context sigma tau
    ((F.relabel j).relabel k) ((A.relabel j).relabel k) ((X.relabel j).relabel k)
    ((gammaCode.relabel j).relabel k) ((function.relabel j).relabel k)
    ((argument.relabel j).relabel k) ((out.relabel j).relabel k) ((parameter.relabel j).relabel k)
    ((targetFunction.relabel j).relabel k) ((vertex.relabel j).relabel k)
    ((G.relabel j).relabel k) ((V.relabel j).relabel k) ((child.relabel j).relabel k)
    (entry.relabel k) pathCode hrec'' he'' hp'' hc'
  have hinc : ∀ h ∈ Gamma, h.relabel (k ∘ j) ∈ Theta := by
    intro h hh
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
      hk (h.relabel j) (hj h hh)
  simp only [Term.relabel_relabel] at result
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
    next gamma (k ∘ j) Theta hinc (entry.relabel k) pathCode result

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateProof.actualOriginalFinalFunctionChildCertificate
