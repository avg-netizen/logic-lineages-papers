module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion OriginalCanonicalFoldFusionSyntaxProof
open OriginalCanonicalFoldFusionBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalBetaTotalityProof
/-- Split only the actual opening guard; every output remains the supplied one. -/
theorem stepAtInput (data : Data) (window : Program 1) (source target : Program 2)
    (closed : ClosedLaw data window source target) (app : ApplicationLaw data window source target)
    (q input typ out parameter : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window source target q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window source target out input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window source target out input typ parameter)) := by
  let accepted := graph2 (InternalParameterizedApplicationResultStack.openGuardP
    (InternalParameterizedCanonicalResultFold.rootGuard data)) (suc z) input parameter
  obtain ⟨hb⟩ := hb
  obtain ⟨hr⟩ := hr
  obtain ⟨hp⟩ := hp
  obtain ⟨hy⟩ := OriginalCanonicalFoldFusionOpeningProof.acceptedAtOutput
    (body := body) (Gamma := accepted :: Gamma) data window source target app q input typ out parameter
    ⟨addHyp hb accepted⟩ ⟨addHyp hr accepted⟩ ⟨addHyp hp accepted⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz : Nonempty (Derivation body (accepted.not :: Gamma)
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard data)) z input parameter)) :=
    InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _
      (Fin.cons input (Fin.cons parameter Fin.elim0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hpn : Nonempty (Derivation body (accepted.not :: Gamma)
      (premises data window source target out input typ parameter)) := ⟨addHyp hp accepted.not⟩
  obtain ⟨hn⟩ := closed body α (accepted.not :: Gamma) out input typ parameter hpn hz
  exact ⟨disjunctionElimination (InternalControlGraphChoiceProof.excludedMiddle accepted)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

/-- Close input, raw type, actual output and unchanged parameter universally. -/
theorem payloadStep (data : Data) (window : Program 1) (source target : Program 2)
    (closed : ClosedLaw data window source target) (app : ApplicationLaw data window source target) (q : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window source target q))) :
    Nonempty (Derivation body Gamma (atPayload data window source target q)) := by
  apply atPayloadIntro data window source target q
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 4) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (α ⊕ Fin 4) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (α ⊕ Fin 4) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (α ⊕ Fin 4) := .var (.inr 3)
  let Delta := premises data window source target out input typ parameter ::
    graph1 InternalUnpair.right (q.relabel Sum.inl) input :: Gamma.map (fun p => p.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 4) Delta (by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput data window source target closed app (q.relabel Sum.inl) input typ out parameter hb'
    (show Nonempty (Derivation body Delta (graph1 InternalUnpair.right (q.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    (show Nonempty (Derivation body Delta (premises data window source target out input typ parameter)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

/-- Original internal strong induction discharges the entire smaller-payload IH. -/
theorem payloadInvariant (data : Data) (window : Program 1) (source target : Program 2)
    (closed : ClosedLaw data window source target) (app : ApplicationLaw data window source target) (payload : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (atPayload data window source target payload)) := by
  apply payloadInduction data window source target payload
  intro β Delta q hb
  exact payloadStep data window source target closed app q hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionInductionProof
