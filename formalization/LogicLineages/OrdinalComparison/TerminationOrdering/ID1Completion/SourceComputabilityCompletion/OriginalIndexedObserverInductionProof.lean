module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalLambdaTraversalSelection OriginalIndexedObserverDefinitions OriginalIndexedObserverSyntaxProof
open OriginalIndexedObserverBindingProof
open OriginalIndexedObserverRangeSyntaxProof (rangeRename)
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
theorem stepAtInput (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K) (lamLaw : LambdaLaw data window K) (supply : OtherLaw data window K)
    (q input typ out parameter mark cutoff : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window K q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter)))
    (hRange : Nonempty (Derivation body Gamma (ActualRange cutoff parameter))) :
    Nonempty (Derivation body Gamma (observations K out input parameter mark cutoff)) := by
  apply OriginalLambdaTraversalTagCasesProof.tagCases input _
  · intro beta j Theta hj ht
    rw [observationsRename]
    have hRange' := renameInto hRange j Theta hj
    rw [rangeRename] at hRange'
    have hb' := renameInto hb j Theta hj
    rw [belowPayloadRename] at hb'
    have hr' := renameInto hr j Theta hj
    rw [graph1Rename] at hr'
    have hp' := renameInto hp j Theta hj
    rw [premisesRename] at hp'
    exact OriginalIndexedObserverApplicationProof.atTag
      OriginalLambdaTraversalInternalApplicationProof.actualOriginalLambdaTraversalInternalApplication
      data window K appLaw (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
      (parameter.relabel j) (mark.relabel j) (cutoff.relabel j) hb' hr' hp' hRange' ht
  · intro beta j Theta hj ht
    rw [observationsRename]
    have hRange' := renameInto hRange j Theta hj
    rw [rangeRename] at hRange'
    have hb' := renameInto hb j Theta hj
    rw [belowPayloadRename] at hb'
    have hr' := renameInto hr j Theta hj
    rw [graph1Rename] at hr'
    have hp' := renameInto hp j Theta hj
    rw [premisesRename] at hp'
    exact OriginalIndexedObserverLambdaProof.atTag
      OriginalLambdaTraversalInternalLambdaProof.actualOriginalLambdaTraversalInternalLambda
      data window K lamLaw (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
      (parameter.relabel j) (mark.relabel j) (cutoff.relabel j) hb' hr' hp' hRange' ht
  · intro beta j Theta hj ht
    rw [observationsRename]
    have hRange' := renameInto hRange j Theta hj
    rw [rangeRename] at hRange'
    have hp' := renameInto hp j Theta hj
    rw [premisesRename] at hp'
    obtain ⟨law⟩ := OriginalLambdaTraversalInternalLeafProof.actualOriginalLambdaTraversalInternalLeaf
      body (leaf data window) beta Theta (input.relabel j) (out.relabel j) (parameter.relabel j)
    obtain ⟨htProof⟩ := ht
    obtain ⟨hc⟩ := InternalApplicationStepPeelSupportProof.andRight
      (InternalApplicationStepPeelSupportProof.andRight hp')
    have hl : Nonempty (Derivation body Theta
        (graph2 (leaf data window) (out.relabel j) (input.relabel j) (parameter.relabel j))) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft
        (Derivation.implicationElimination law htProof)) hc⟩
    exact supply body beta Theta (out.relabel j) (input.relabel j) (typ.relabel j)
      (parameter.relabel j) (mark.relabel j) (cutoff.relabel j) hRange' (InternalApplicationStepPeelSupportProof.andLeft hp')
      (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hp'))
      ⟨htProof⟩ hl


/-- Close input, raw type, actual output, parameter and every observer mark universally. -/
theorem payloadStep (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K) (lamLaw : LambdaLaw data window K) (supply : OtherLaw data window K) (q : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window K q))) :
    Nonempty (Derivation body Gamma (atPayload data window K q)) := by
  apply atPayloadIntro data window K q
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 6) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (α ⊕ Fin 6) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (α ⊕ Fin 6) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (α ⊕ Fin 6) := .var (.inr 3)
  let mark : OrdinaryArithmetic.Term (α ⊕ Fin 6) := .var (.inr 4)
  let cutoff : OrdinaryArithmetic.Term (α ⊕ Fin 6) := .var (.inr 5)
  let Delta := ActualRange cutoff parameter :: premises data window out input typ parameter ::
    graph1 InternalUnpair.right (q.relabel Sum.inl) input :: Gamma.map (fun p => p.relabel Sum.inl)
  have hb' := renameInto hb (Sum.inl : α → α ⊕ Fin 6) Delta (by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  rw [belowPayloadRename] at hb'
  obtain ⟨h⟩ := stepAtInput data window K appLaw lamLaw supply (q.relabel Sum.inl) input typ out parameter mark cutoff hb'
    (show Nonempty (Derivation body Delta (graph1 InternalUnpair.right (q.relabel Sum.inl) input)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩)
    (show Nonempty (Derivation body Delta (premises data window out input typ parameter)) from
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    (show Nonempty (Derivation body Delta (ActualRange cutoff parameter)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))⟩

/-- Original internal strong induction discharges the entire smaller-payload IH. -/
theorem payloadObservers (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K) (lamLaw : LambdaLaw data window K) (supply : OtherLaw data window K) (payload : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (atPayload data window K payload)) := by
  apply payloadInduction data window K payload
  intro β Delta q hb
  exact payloadStep data window K appLaw lamLaw supply q hb

theorem observationsAtInput (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K) (lamLaw : LambdaLaw data window K) (supply : OtherLaw data window K)
    (out input typ parameter mark cutoff : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter)))
    (hRange : Nonempty (Derivation body Gamma (ActualRange cutoff parameter))) :
    Nonempty (Derivation body Gamma (observations K out input parameter mark cutoff)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro beta j Theta payload hj hr
  rw [observationsRename]
  have hRange' := renameInto hRange j Theta hj
  rw [rangeRename] at hRange'
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact atPayloadApply data window K payload (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) (mark.relabel j) (cutoff.relabel j)
    (payloadObservers data window K appLaw lamLaw supply payload) hr hp' hRange'


theorem actualIndexedObserverTraversal : OriginalIndexedObserverTargets.ActualIndexedObserverTraversal := by
  intro data window K appLaw lamLaw supply body alpha Delta out input typ parameter mark cutoff
  let A := premises data window out input typ parameter ⊓ ActualRange cutoff parameter
  obtain ⟨h⟩ := observationsAtInput (body := body) (Gamma := A :: Delta)
    data window K appLaw lamLaw supply out input typ parameter mark cutoff
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverInductionProof
