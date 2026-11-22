module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename inputsRename)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentMemoGrammarTargets (ArgumentHit)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (keepThrough)
open NumberedWindowInternalCoverArgumentGrammarInductionBindingProof (argumentExistsRename)
open NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof (consumeArgument)
open NumberedWindowInternalCoverArgumentGrammarInductionPlacementProof (moveArgumentHit actualArgumentFromHead)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem withTail (F G : Program 1) (s : Settings) (h a mt dt wt ts tts tas : OTerm α)
    (provider : HeadProvider F G s body)
    (headOK : Nonempty (Derivation body Γ (unary G (suc z) h)))
    (tailMeasured : Nonempty (Derivation body Γ (unary (argumentMeasure F) mt a)))
    (tailPair : Nonempty (Derivation body Γ (codePair mt dt wt)))
    (tailHit : ArgumentHit s body Γ dt wt ts tts tas a) :
    Nonempty (Derivation body Γ (argumentExists F s (rawCons h a))) := by
  let A := argumentMeasure F
  let Q := argumentExists F s (rawCons h a)
  apply programCases F ![h] Q
  intro β j Δ mh keep head
  apply programCases A ![rawCons (h.relabel j) (a.relabel j)] (Q.relabel j)
  intro γ g Ξ out retain parent
  let k := g ∘ j
  have both := keepThrough j g keep retain
  have head' := renameInto head g Ξ retain
  simp only [programRename,inputsRename,Term.relabel_relabel] at head'
  simp only [inputsRename,rawConsRename,Term.relabel_relabel] at parent
  have ok := renameInto headOK k Ξ both
  simp only [unaryRename,sucRelabel,zRelabel] at ok
  have tail := renameInto tailMeasured k Ξ both
  rw [unaryRename] at tail
  have pairs := renameInto tailPair k Ξ both
  rw [pairRename] at pairs
  have placed := moveArgumentHit s dt wt ts tts tas a k Ξ both tailHit
  rw [formulaRelabelComposition j g Q]
  simp only [Q,argumentExistsRename,rawConsRename]
  exact actualArgumentFromHead F G s (h.relabel k) (a.relabel k) out (mh.relabel g) (mt.relabel k)
    (dt.relabel k) (wt.relabel k) (ts.relabel k) (tts.relabel k) (tas.relabel k)
    provider ok parent head' tail pairs placed

theorem actualArgumentGrammarFromTail (F G : Program 1) (s : Settings) (h a : OTerm α)
    (provider : HeadProvider F G s body)
    (headOK : Nonempty (Derivation body Γ (unary G (suc z) h)))
    (tail : Nonempty (Derivation body Γ (argumentExists F s a))) :
    Nonempty (Derivation body Γ (argumentExists F s (rawCons h a))) := by
  apply consumeArgument F s a (argumentExists F s (rawCons h a)) tail
  intro β j Δ p d w st terms args keep measured pair hit
  have hh := renameInto headOK j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at hh
  simp only [argumentExistsRename,rawConsRename]
  exact withTail F G s (h.relabel j) (a.relabel j) p d w st terms args
    provider hh measured pair hit

#print axioms actualArgumentGrammarFromTail

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionConsProof
