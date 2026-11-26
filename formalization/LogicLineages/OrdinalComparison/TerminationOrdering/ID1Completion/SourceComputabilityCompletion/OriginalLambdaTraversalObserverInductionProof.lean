module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverApplicationInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLambdaInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalLambdaTraversalSelection OriginalLambdaTraversalObserver OriginalLambdaTraversalObserverSyntaxProof
open OriginalLambdaTraversalObserverBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalBetaTotalityProof
/-- Exhaust the actual raw constructor tags. Every machine recurrence
supplier here is the independently checked unconditional internal theorem. -/
theorem stepAtInput (data : Data) (window : Program 1)
    (q input typ out parameter mark : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter))) :
    Nonempty (Derivation body Gamma (observations out input mark)) := by
  apply OriginalLambdaTraversalTagCasesProof.tagCases input _
  · intro beta j Theta hj ht
    rw [observationsRename]
    have hb' := renameInto hb j Theta hj
    rw [belowPayloadRename] at hb'
    have hr' := renameInto hr j Theta hj
    rw [graph1Rename] at hr'
    have hp' := renameInto hp j Theta hj
    rw [premisesRename] at hp'
    exact OriginalLambdaTraversalObserverApplicationInductionProof.atTag
      OriginalLambdaTraversalInternalApplicationProof.actualOriginalLambdaTraversalInternalApplication
      data window (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
      (parameter.relabel j) (mark.relabel j) hb' hr' hp' ht
  · intro beta j Theta hj ht
    rw [observationsRename]
    have hp' := renameInto hp j Theta hj
    rw [premisesRename] at hp'
    exact OriginalLambdaTraversalObserverLambdaInductionProof.atTag
      data window (input.relabel j) (typ.relabel j) (out.relabel j)
      (parameter.relabel j) (mark.relabel j) hp' ht
  · intro beta j Theta hj ht
    rw [observationsRename]
    have hp' := renameInto hp j Theta hj
    rw [premisesRename] at hp'
    exact OriginalLambdaTraversalObserverLeafProof.atOtherTag
      data window (out.relabel j) (input.relabel j) (typ.relabel j)
      (parameter.relabel j) (mark.relabel j) hp' ht

/-- Close input, raw type, actual output, parameter and every observer mark universally. -/
theorem payloadStep (data : Data) (window : Program 1) (q : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q))) :
    Nonempty (Derivation body Gamma (atPayload data window q)) := by
  apply atPayloadIntro data window q
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 3)
  let mark : OrdinaryArithmetic.Term (α ⊕ Fin 5) := .var (.inr 4)
  let Delta := premises data window out input typ parameter ::
    graph1 InternalUnpair.right (q.relabel Sum.inl) input :: Gamma.map (fun p => p.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 5) Delta (by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput data window (q.relabel Sum.inl) input typ out parameter mark hb'
    (show Nonempty (Derivation body Delta (graph1 InternalUnpair.right (q.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    (show Nonempty (Derivation body Delta (premises data window out input typ parameter)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

/-- Original internal strong induction discharges the entire smaller-payload IH. -/
theorem payloadObservers (data : Data) (window : Program 1) (payload : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (atPayload data window payload)) := by
  apply payloadInduction data window payload
  intro β Delta q hb
  exact payloadStep data window q hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverInductionProof
