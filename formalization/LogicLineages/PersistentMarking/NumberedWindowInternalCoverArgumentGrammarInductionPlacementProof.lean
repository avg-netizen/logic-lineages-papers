module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets (ArgumentHit ActualHeadAndTail)
open NumberedWindowInternalCoverArgumentMemoGrammarProof (exact_OpenCoverArgumentMemoGrammar)
open NumberedWindowInternalCoverArgumentGrammarInductionBindingProof (argumentExistsRename)
open NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof (introduceArgument)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveArgumentHit {β : Type} (s : Settings) (d w st terms args key : OTerm α)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (actual : ArgumentHit s body Γ d w st terms args key) :
    ArgumentHit s body Δ (d.relabel j) (w.relabel j) (st.relabel j) (terms.relabel j) (args.relabel j) (key.relabel j) := by
  have scope := renameInto actual.scope j Δ keep
  simp only [observedRename,headsTerm,typesTerm,numeralRename] at scope
  have proven := renameInto actual.hit j Δ keep
  rw [graphRename] at proven
  exact ⟨scope,proven⟩

theorem actualArgumentFromHead (F G : Program 1) (s : Settings)
    (h a out mh mt dt wt ts tts tas : OTerm α)
    (provider : HeadProvider F G s body)
    (guard : Nonempty (Derivation body Γ (unary G (suc (ID1Completion.InternalTagArithmeticSyntaxProof.z)) h)))
    (report : Nonempty (Derivation body Γ (unary (argumentMeasure F) out (rawCons h a))))
    (hd : Nonempty (Derivation body Γ (unary F mh h)))
    (tl : Nonempty (Derivation body Γ (unary (argumentMeasure F) mt a)))
    (typePair : Nonempty (Derivation body Γ (codePair mt dt wt)))
    (tailHit : ArgumentHit s body Γ dt wt ts tts tas a) :
    Nonempty (Derivation body Γ (argumentExists F s (rawCons h a))) := by
  let Q := argumentExists F s (rawCons h a)
  apply provider α Γ h mh Q guard hd
  intro β j Δ dh wh hs hts has keep hp hit
  let h' := h.relabel j
  let a' := a.relabel j
  let out' := out.relabel j
  have measured := renameInto report j Δ keep
  simp only [unaryRename,rawConsRename] at measured
  have t := moveArgumentHit s dt wt ts tts tas a j Δ keep tailHit
  have paid : ActualHeadAndTail F body Δ h' a' out'
      (mh.relabel j) (mt.relabel j) dh wh (dt.relabel j) (wt.relabel j) := by
    have hRep := renameInto hd j Δ keep
    have tRep := renameInto tl j Δ keep
    have tPair := renameInto typePair j Δ keep
    simp only [unaryRename] at hRep tRep
    simp only [pairRename] at tPair
    exact ⟨measured,hRep,tRep,hp,tPair⟩
  apply exact_OpenCoverArgumentMemoGrammar F s body β Δ h' a' out' (mh.relabel j) (mt.relabel j)
    dh wh (dt.relabel j) (wt.relabel j) hs hts has (ts.relabel j) (tts.relabel j) (tas.relabel j)
    (Q.relabel j) paid hit t
  intro γ g Ξ w state terms args retain pair placed
  have p := renameInto measured g Ξ retain
  simp only [unaryRename,rawConsRename] at p
  rw [formulaRelabelComposition j g Q]
  simp only [Q,argumentExistsRename,rawConsRename]
  simp only [h',a',out',Term.relabel_relabel] at p pair placed
  exact introduceArgument F s (rawCons (h.relabel (g ∘ j)) (a.relabel (g ∘ j)))
    (out.relabel (g ∘ j)) (suc (add (dh.relabel g) (dt.relabel (g ∘ j)))) w
    state terms args p pair placed

#print axioms actualArgumentFromHead

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof
