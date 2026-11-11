module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion OriginalCanonicalFoldFusionSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
open OriginalCanonicalFoldFusionBindingProof
open InternalSquareRootArithmeticSupportProof
/-- The induction is applied at both original strictly smaller right payloads.
The actual output witnesses are unrelated to the old fp/ap fields. -/
theorem openingAtOutputs (data : Data) (window : Program 1) (source target : Program 2)
    (app : ApplicationLaw data window source target)
    (q input typ parameter payload arrow d e fp ap fn arg functionOut argumentOut out : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window source target q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window source target out input typ parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Gamma (InternalLessThan.strictLess ap payload)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedCanonicalResultFold.rootGuard data) (suc z) input parameter)))
    (hf : Nonempty (Derivation body Gamma (graph2 source functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 source argumentOut arg parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out input typ parameter)) := by
  have guards := InternalParameterizedCanonicalResultFoldOpeningProof.rootGuardRecover
    data arrow d e fp ap fn arg input parameter hc hg
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload q (Fin.cons input Fin.elim0) hpr hr
  obtain ⟨hfl⟩ := hfl
  obtain ⟨hal⟩ := hal
  have hfw := OriginalApplicationSidecarWindowProof.windowTransfer window
    InternalOriginalStepGuard.one input fn parameter (andLeft hp)
  have haw := OriginalApplicationSidecarWindowProof.windowTransfer window
    InternalOriginalStepGuard.one input arg parameter (andLeft hp)
  have hfi := belowPayloadApply data window source target q fp fn arrow functionOut parameter hb
    ⟨orderRight fp hep hfl⟩ hfr
    (andIntro hfw (andIntro (andIntro (andLeft (andRight guards))
      (pairLeft fn arrow fp (andLeft (andRight hc)))) hf))
  have hai := belowPayloadApply data window source target q ap arg d argumentOut parameter hb
    ⟨orderRight ap hep hal⟩ har
    (andIntro haw (andIntro (andIntro (andLeft (andRight (andRight guards)))
      (pairLeft arg d ap (andLeft (andRight (andRight hc))))) ha))
  exact app body α Gamma arrow d e fp ap fn arg input functionOut argumentOut out typ parameter
    hc hp hf ha hfi hai

/-- Two ordinary Program queries bind actual C outputs at the same parameter.
No child-success or invariant is assumed: both triples follow from the IH. -/
theorem openingWithOutputs (data : Data) (window : Program 1) (source target : Program 2)
    (app : ApplicationLaw data window source target)
    (q input typ out parameter payload arrow d e fp ap fn arg : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window source target q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window source target out input typ parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Gamma (InternalLessThan.strictLess ap payload)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedCanonicalResultFold.rootGuard data) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out input typ parameter)) := by
  apply OriginalApplicationSidecarInvariantQueryProof.binaryPairOutputCases
    source fn arg parameter _
  intro β j Delta functionOut argumentOut hj hf ha
  rw [outputInvariantRename]
  have hb' := renameInto hb j Delta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hpr' := renameInto hpr j Delta hj
  have hfr' := renameInto hfr j Delta hj
  have har' := renameInto har j Delta hj
  rw [graph1Rename] at hpr' hfr' har'
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  unfold InternalLessThan.strictLess at hfl' hal'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
  have hg' := renameInto hg j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  exact openingAtOutputs data window source target app (q.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) (payload.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) functionOut argumentOut (out.relabel j)
    hb' hr' hp' hc' hpr' hfr' har' hfl' hal' hg' hf ha

/-- Original opening inversion supplies all constructor and strict-bound data. -/
theorem acceptedAtOutput (data : Data) (window : Program 1) (source target : Program 2)
    (app : ApplicationLaw data window source target)
    (q input typ out parameter : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window source target q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window source target out input typ parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard data)) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out input typ parameter)) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalParameterizedCanonicalResultFold.rootGuard data) input parameter _ hg
  intro β j Delta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal hguard
  rw [outputInvariantRename]
  have hb' := renameInto hb j Delta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  exact openingWithOutputs data window source target app (q.relabel j) (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) payload arrow d e fp ap fn arg
    hb' hr' hp' hc hpr hfr har hfl hal hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionOpeningProof
