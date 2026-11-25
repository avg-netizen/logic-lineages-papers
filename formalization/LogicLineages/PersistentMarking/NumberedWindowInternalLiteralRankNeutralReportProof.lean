module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileObserversProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastSelectedObserverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankNeutralReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue zeroConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast addressGood)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalRankMeasuredExchangeOpenProof (exact_OpenRankMeasuredPackedEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalLiteralLeastSelectedObserverProof (exact_OpenLiteralSelectedObserver)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def addressRank (H : Program 1) : Program 1 :=
  .composition H (Fin.cons rawLeast Fin.elim0)

def isPositiveRank (H : Program 1) : Program 1 :=
  branch (addressRank H) (constantZero 1) (constantOne 1)

/-- A rank-based neutral predicate for the same physical rank tuple.
This is not definitionally the earlier non-lambda header recognizer. -/
def rankNeutral (H : Program 1) : Program 1 := conjunction addressGood (isPositiveRank H)

private theorem reportAtAddress (H : Program 1) (x ctx ty q rank : OTerm α)
    (addr : D B Γ (addressReport x ctx ty q))
    (held : D B Γ (unary H rank q)) : D B Γ (unary (addressRank H) rank x) := by
  obtain ⟨r⟩ := addr
  apply compositionValue H (Fin.cons rawLeast Fin.elim0) rank ![x] ![q] held
  intro i
  obtain rfl := Fin.eq_zero i
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩

theorem exact_OpenRankNeutralFromRaw (H : Program 1) (x ctx ty q r : OTerm α)
    (address : D B Γ (addressReport x ctx ty q))
    (rank : D B Γ (unary H (suc r) q)) : D B Γ (atom (rankNeutral H) x) := by
  obtain ⟨addr⟩ := address
  have positive := successorBranchIntro (addressRank H) (constantZero 1) (constantOne 1) (suc z) r ![x]
    (reportAtAddress H x ctx ty q (suc r) ⟨addr⟩ rank) (oneConstantValue ![x])
  exact conjunctionAccept addressGood (isPositiveRank H) ![x] ⟨Derivation.conjunctionLeft addr⟩ positive

theorem exact_OpenRankNeutralRejectsZero (H : Program 1) (x ctx ty q : OTerm α)
    (address : D B Γ (addressReport x ctx ty q))
    (neutral : D B Γ (atom (rankNeutral H) x)) (none : D B Γ (unary H z q)) :
    D B Γ ⊥ := by
  obtain ⟨checks⟩ := conjunctionRecover addressGood (isPositiveRank H) ![x] neutral
  have bad := zeroBranchElim (addressRank H) (constantZero 1) (constantOne 1) (suc z) ![x]
    (reportAtAddress H x ctx ty q z address none) ⟨Derivation.conjunctionRight checks⟩
  obtain ⟨eq⟩ := valueUnique (constantZero 1) (suc z) z ![x] bad (zeroConstantValue ![x])
  exact ⟨sucNeZeroApply eq⟩

/-- The physical rank comparison already present in the chosen
four-slot rank edge transports its actual open output; no new
numeric equivalence is used. -/
theorem exact_OpenRankObserver (C W : Program 3) (s : Settings) (H : Program 1) (D₀ : Program 2) :
    Preserves (edge4 (rankedExchange C s H D₀) W) (unaryObserver H) := by
  intro B α Γ ctx ty a b r edge seen
  obtain ⟨rule⟩ := exact_OpenRankMeasuredPackedEdge C W s H D₀ B α Γ ctx ty r a b
  obtain ⟨edge⟩ := edge
  obtain ⟨value⟩ := exact_OpenUnaryObserverElim H ctx ty a r seen
  exact exact_OpenUnaryObserverIntro H ctx ty b r
    ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction edge value)⟩

theorem exact_OpenSelectedRank (C W : Program 3) (s : Settings) (H : Program 1) (D₀ : Program 2)
    (ctx ty q chosen value : OTerm α)
    (least : D B Γ (leastGraph C (rankedExchange C s H D₀) W s ctx ty q chosen))
    (held : D B Γ (unary H value q)) : D B Γ (unary H value chosen) :=
  exact_OpenUnaryObserverElim H ctx ty chosen value
    (exact_OpenLiteralSelectedObserver C (rankedExchange C s H D₀) W s (unaryObserver H)
      (exact_OpenRankObserver C W s H D₀) ctx ty q chosen value least
      (exact_OpenUnaryObserverIntro H ctx ty q value held))

#print axioms exact_OpenRankNeutralFromRaw
#print axioms exact_OpenRankNeutralRejectsZero
#print axioms exact_OpenRankObserver
#print axioms exact_OpenSelectedRank
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankNeutralReportProof
