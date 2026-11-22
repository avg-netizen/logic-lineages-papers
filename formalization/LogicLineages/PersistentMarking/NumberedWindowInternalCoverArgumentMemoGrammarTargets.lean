module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSharedOwnScratchTargets (OwnOccurrence)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)

structure ActualHeadAndTail (F : Program 1) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (h a p mh mt dh wh dt wt : OTerm α) : Prop where
  cons : Nonempty (Derivation body Γ (unary (argumentMeasure F) p (rawCons h a)))
  head : Nonempty (Derivation body Γ (unary F mh h))
  tail : Nonempty (Derivation body Γ (unary (argumentMeasure F) mt a))
  headPair : Nonempty (Derivation body Γ (codePair mh dh wh))
  tailPair : Nonempty (Derivation body Γ (codePair mt dt wt))

def ExactOpenCoverArgumentMemoBounds : Prop :=
  ∀ (F : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p mh mt dh wh dt wt : OTerm α),
    ActualHeadAndTail F body Γ h a p mh mt dh wh dt wt →
    Nonempty (Derivation body Γ (existsOne (boundBody p dh dt wh wt)))

/-- The tail's occurrence is on the actual **argument** list, not terms. -/
structure ArgumentHit (s : Settings) (body : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (d w state terms args key : OTerm α) : Prop where
  scope : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) w state terms args))
  hit : Nonempty (Derivation body Γ (memberGraph args key))

/-- The actual physical argument pair and chosen occurrence are delivered
together. Both recursive observations/hits remain genuine premises. -/
def ExactOpenCoverArgumentMemoGrammar : Prop :=
  ∀ (F : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h a p mh mt dh wh dt wt hs hts has ts tts tas : OTerm α) (goal : Formula α),
    ActualHeadAndTail F body Γ h a p mh mt dh wh dt wt →
    OwnOccurrence s body Γ dh wh hs hts has h →
    ArgumentHit s body Γ dt wt ts tts tas a →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (codePair (p.relabel j) (suc (add (dh.relabel j) (dt.relabel j))) w)) →
      ArgumentHit s body Δ (suc (add (dh.relabel j) (dt.relabel j))) w state terms args
        (rawCons (h.relabel j) (a.relabel j)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarTargets
