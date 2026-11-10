module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarSpine OriginalApplicationSidecarSpineSyntaxProof
open OriginalApplicationSidecarSpineBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalBetaTotalityProof
/-- Split only the actual opening guard; every output remains the supplied one. -/
theorem stepAtInput (data : Data) (window : Program 1)
    (q input typ out parameter value : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  let accepted := graph2 (InternalParameterizedApplicationResultStack.openGuardP
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) (suc z) input parameter
  obtain ⟨hb⟩ := hb
  obtain ⟨hr⟩ := hr
  obtain ⟨hp⟩ := hp
  obtain ⟨hy⟩ := OriginalApplicationSidecarSpineOpeningProof.acceptedAtOutput
    (body := body) (Gamma := accepted :: Gamma) data window q input typ out parameter value
    ⟨addHyp hb accepted⟩ ⟨addHyp hr accepted⟩ ⟨addHyp hp accepted⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz : Nonempty (Derivation body (accepted.not :: Gamma)
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) z input parameter)) :=
    InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
      (Fin.cons input (Fin.cons parameter Fin.elim0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hpn : Nonempty (Derivation body (accepted.not :: Gamma)
      (premises data window out input typ parameter)) := ⟨addHyp hp accepted.not⟩
  obtain ⟨hn⟩ := OriginalApplicationSidecarSpineLeafProof.rejectedSpineIff
    (body := body) (Delta := accepted.not :: Gamma) data window out input parameter value
    (InternalApplicationStepPeelSupportProof.andLeft hpn)
    (InternalApplicationStepPeelSupportProof.andLeft
      (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hpn)))
    (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hpn)) hz
  exact ⟨disjunctionElimination (InternalControlGraphChoiceProof.excludedMiddle accepted)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Close all FIVE input/type/output/parameter/observer variables universally. -/
theorem payloadStep (data : Data) (window : Program 1) (q : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q))) :
    Nonempty (Derivation body Gamma (atPayload data window q)) := by
  apply atPayloadIntro data window q
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 3)
  let value : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 4)
  let Delta := premises data window out input typ parameter ::
    graph1 InternalUnpair.right (q.relabel Sum.inl) input :: Gamma.map (fun p => p.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 5) Delta (by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput data window (q.relabel Sum.inl) input typ out parameter value hb'
    (show Nonempty (Derivation body Delta (graph1 InternalUnpair.right (q.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    (show Nonempty (Derivation body Delta (premises data window out input typ parameter)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

/-- Original internal strong induction discharges the entire smaller-payload IH. -/
theorem payloadSpine (data : Data) (window : Program 1) (payload : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (atPayload data window payload)) := by
  apply payloadInduction data window payload
  intro β Delta q hb
  exact payloadStep data window q hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineInductionProof
