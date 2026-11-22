module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalStrongInduction (below)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSharedOwnScratchTargets (OwnOccurrence)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)

abbrev argumentPayload (F : Program 1) (s : Settings) {α : Type} (raw : OTerm α) (vals : Fin 6 → OTerm α) :
    Formula α :=
  unary (argumentMeasure F) (vals 0) raw ⊓
    (codePair (vals 0) (vals 1) (vals 2) ⊓
      (observed (vals 1) (headsTerm s α) (typesTerm s α) (vals 2) (vals 3) (vals 4) (vals 5) ⊓
        memberGraph (vals 5) raw))

def argumentMatrix (F : Program 1) (s : Settings) {α : Type} (raw : OTerm α) : Formula (α ⊕ Fin 6) :=
  argumentPayload F s (raw.relabel Sum.inl) (fun i => .var (.inr i))

def argumentExists (F : Program 1) (s : Settings) {α : Type} (raw : OTerm α) : Formula α :=
  block (argumentMatrix F s raw)

def argumentAt (F G : Program 1) (s : Settings) {α : Type} (raw : OTerm α) : Formula α :=
  (unary (argumentReject G) z raw).imp (argumentExists F s raw)

def argumentMotive (F G : Program 1) (s : Settings) {α : Type} : Formula (α ⊕ Fin 1) :=
  argumentAt F G s (.var (.inr 0))

/-- The explicit remaining source premise: a real head report of G and
a real head measurement of F yield the pair and actual term grammar
occurrence for that particular head. This does not get a tail premise. -/
def HeadProvider (F G : Program 1) (s : Settings) (body : Positive (Fin 1)) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (head p : OTerm α) (Q : Formula α),
    Nonempty (Derivation body Γ (unary G (suc z) head)) →
    Nonempty (Derivation body Γ (unary F p head)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d w state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (codePair (p.relabel j) d w)) →
      OwnOccurrence s body Δ d w state terms args (head.relabel j) →
      Nonempty (Derivation body Δ (Q.relabel j))) →
    Nonempty (Derivation body Γ Q)

def ExactOpenCoverArgumentGrammarInduction : Prop :=
  ∀ (F G : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (raw : OTerm α),
    HeadProvider F G s body →
    Nonempty (Derivation body Γ (unary (argumentReject G) z raw)) →
    Nonempty (Derivation body Γ (argumentExists F s raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
