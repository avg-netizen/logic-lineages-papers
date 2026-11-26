module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoGrammarTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentCell argumentHead tailMeasure)
open NumberedWindowFieldAlgorithm (unpack)

def argumentHeadAccept (G : Program 1) : Program 4 := unaryAfter G argumentHead
def argumentTailAccept : Program 4 := unaryAfter GorbowPRInternalControl.zeroTest tailMeasure
def argumentGuard (G : Program 1) : Program 4 :=
  conjunction argumentCell (conjunction (argumentHeadAccept G) argumentTailAccept)

/-- Actual reversed polarity: 0 accepted, 1 rejected. The selected nil
row is already zero. A malformed positive gap reaches literal one. -/
def argumentRejectUpdate (G : Program 1) : Program 4 :=
  branch (GorbowVerifierNormalization.normalize (argumentGuard G)) (literal 4 1) (constantZero 4)

abbrev argumentReject (G : Program 1) : Program 1 := selectedMeasure (argumentRejectUpdate G)

def acceptedHeads (G : Program 1) (raw : Nat) : Bool :=
  (unpack raw).any (fun xs => xs.all (fun h => evaluate G (h ::ᵥ nil) == 1))

def ExactCoverArgumentGuardNumeric : Prop :=
  ∀ (G : Program 1) (raw : Nat),
    evaluate (argumentReject G) (raw ::ᵥ nil) = if acceptedHeads G raw then 0 else 1

/-- Genuine source shape inversion for the exact selected guard. The
same guard G is observed at the stored head, and the same argument
memo supplies zero rejection report at the physically earlier tail. -/
def ExactOpenCoverArgumentGuardCases : Prop :=
  ∀ (G : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (argumentReject G) z raw)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (z : OTerm β))) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h a : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (eqn (raw.relabel j) (rawCons h a))) →
      Nonempty (Derivation body Δ (ltF a (raw.relabel j))) →
      Nonempty (Derivation body Δ (unary G (suc z) h)) →
      Nonempty (Derivation body Δ (unary (argumentReject G) z a)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
