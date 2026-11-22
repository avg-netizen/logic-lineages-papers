module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarPlacementProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (add impSubst)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarCrossBoundProof (exact_OpenSelectedGrammarCrossBound)
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsStageProof (exact_OpenSelectedNonemptyArgsFromPredecessor)
open NumberedWindowInternalCoverSharedOwnScratchTargets (OwnOccurrence)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (boundReport)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem transfer (old next key : OTerm α)
    (inc : Derivation body Γ (axisInclusion old next))
    (hit : Nonempty (Derivation body Γ (memberGraph old key))) :
    Nonempty (Derivation body Γ (memberGraph next key)) := by
  have law : Derivation body Γ ((memberGraph old key).imp (memberGraph next key)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using
      (Derivation.universalElimination (emb key) inc)
  obtain ⟨hit⟩ := hit
  exact ⟨Derivation.implicationElimination law hit⟩

theorem actualArgumentMemoGrammarPlacement (s : Settings)
    (h a p dh wh dt wt w hs hts has ts tts tas mid mids mida state terms args : OTerm α)
    (head : OwnOccurrence s body Γ dh wh hs hts has h)
    (tail : ArgumentHit s body Γ dt wt ts tts tas a)
    (bounds : Nonempty (Derivation body Γ (boundReport p dh dt wh wt w)))
    (before : Nonempty (Derivation body Γ (observed (add dh dt) (headsTerm s α) (typesTerm s α) w mid mids mida)))
    (after : Nonempty (Derivation body Γ (observed (suc (add dh dt)) (headsTerm s α) (typesTerm s α) w state terms args))) :
    ArgumentHit s body Γ (suc (add dh dt)) w state terms args (rawCons h a) := by
  let d := add dh dt
  let H := headsTerm s α
  let K := typesTerm s α
  obtain ⟨report⟩ := bounds
  have deps := Derivation.conjunctionLeft (Derivation.conjunctionRight report)
  have wids := Derivation.conjunctionRight (Derivation.conjunctionRight report)
  obtain ⟨headInc⟩ := exact_OpenSelectedGrammarCrossBound body α Γ dh d H K wh w
    hs hts has mid mids mida ⟨Derivation.conjunctionLeft deps⟩ ⟨Derivation.conjunctionLeft wids⟩
    head.observedScope before
  obtain ⟨tailInc⟩ := exact_OpenSelectedGrammarCrossBound body α Γ dt d H K wt w
    ts tts tas mid mids mida ⟨Derivation.conjunctionRight deps⟩ ⟨Derivation.conjunctionRight wids⟩
    tail.scope before
  have h' := transfer hts mids h (Derivation.conjunctionLeft headInc) head.ownKey
  have a' := transfer tas mida a (Derivation.conjunctionRight tailInc) tail.hit
  exact ⟨after,exact_OpenSelectedNonemptyArgsFromPredecessor body α Γ d H K w
    mid mids mida state terms args h a before after h' a'⟩

#print axioms actualArgumentMemoGrammarPlacement

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarPlacementProof
