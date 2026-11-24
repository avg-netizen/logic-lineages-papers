module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredExchangeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredPackedEdgeComparisonProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (exchangeTape edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange swapExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredExchangeThinOpenCompareProof (compareShared)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem swapGraph (D : Program 2) (a b : OTerm α) :
    Nonempty (Derivation B Γ (programGraph (swapExchange D) (suc z) (exchangeTape a b))) ↔
    Nonempty (Derivation B Γ (programGraph D (suc z) (exchangeTape b a))) := by
  let xs := exchangeTape a b
  let ys := exchangeTape b a
  let ps : Fin 2 → Program 2 := ![.projection 1,.projection 0]
  have pr (i : Fin 2) : Nonempty (Derivation B Γ (programGraph (ps i) (ys i) xs)) :=
    Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 0 xs) (fun k => Fin.elim0 k)) i
  exact ⟨fun h => compositionRecover D ps (suc z) xs ys h pr,
    fun h => compositionValue D ps (suc z) xs ys h pr⟩

/-- Forget an inserted rank test on a literal packed edge. The original
paired reports, cover comparison and both typed windows are retained. -/
theorem exact_OpenForgetRankMeasuredPackedEdge (C W : Program 3) (s : Settings)
    (rank : Program 1) (D : Program 2) (ctx ty a b : OTerm α)
    (held : Nonempty (Derivation B Γ (acceptEdge (edge4 (rankedExchange C s rank D) W) ctx ty a b))) :
    Nonempty (Derivation B Γ (acceptEdge (edge4 (guardedExchange C s (pairedExchange D)) W) ctx ty a b)) := by
  let Y := measuredExchange rank D
  let A := rankedExchange C s rank D
  let X := guardedExchange C s (pairedExchange D)
  obtain ⟨lawA⟩ := exact_OpenPackedScalarEdge A W B α Γ ctx ty a b
  obtain ⟨lawX⟩ := exact_OpenPackedScalarEdge X W B α Γ ctx ty a b
  obtain ⟨h⟩ := held
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawA) h
  obtain ⟨g⟩ := conjunctionRecover (pairedExchange Y) (compareOptions C s) (exchangeTape a b) ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pair⟩ := conjunctionRecover Y (swapExchange Y) (exchangeTape a b) ⟨Derivation.conjunctionLeft g⟩
  obtain ⟨p⟩ := conjunctionRecover D (compareMeasurements rank) (exchangeTape a b) ⟨Derivation.conjunctionLeft pair⟩
  obtain ⟨q⟩ := conjunctionRecover D (compareMeasurements rank) (exchangeTape b a)
    ((swapGraph Y a b).mp ⟨Derivation.conjunctionRight pair⟩)
  have both := conjunctionAccept D (swapExchange D) (exchangeTape a b) ⟨Derivation.conjunctionLeft p⟩
    ((swapGraph D a b).mpr ⟨Derivation.conjunctionLeft q⟩)
  obtain ⟨accept⟩ := conjunctionAccept (pairedExchange D) (compareOptions C s) (exchangeTape a b)
    both ⟨Derivation.conjunctionRight g⟩
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight lawX)
    (Derivation.conjunctionIntroduction accept (Derivation.conjunctionRight calls))⟩

/-- Reinsert the genuine rank tests on both swapped tapes from a shared
actual output, without reflecting the numerical calibration. -/
theorem exact_OpenInsertRankMeasuredPackedEdge (C W : Program 3) (s : Settings)
    (rank : Program 1) (D : Program 2) (ctx ty a b r : OTerm α)
    (held : Nonempty (Derivation B Γ (acceptEdge (edge4 (guardedExchange C s (pairedExchange D)) W) ctx ty a b)))
    (ra : Nonempty (Derivation B Γ (unary rank r a)))
    (rb : Nonempty (Derivation B Γ (unary rank r b))) :
    Nonempty (Derivation B Γ (acceptEdge (edge4 (rankedExchange C s rank D) W) ctx ty a b)) := by
  let Y := measuredExchange rank D
  let A := rankedExchange C s rank D
  let X := guardedExchange C s (pairedExchange D)
  obtain ⟨lawX⟩ := exact_OpenPackedScalarEdge X W B α Γ ctx ty a b
  obtain ⟨lawA⟩ := exact_OpenPackedScalarEdge A W B α Γ ctx ty a b
  obtain ⟨h⟩ := held
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawX) h
  obtain ⟨g⟩ := conjunctionRecover (pairedExchange D) (compareOptions C s) (exchangeTape a b) ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pair⟩ := conjunctionRecover D (swapExchange D) (exchangeTape a b) ⟨Derivation.conjunctionLeft g⟩
  have p := conjunctionAccept D (compareMeasurements rank) (exchangeTape a b)
    ⟨Derivation.conjunctionLeft pair⟩ (compareShared rank a b r ra rb)
  have q := conjunctionAccept D (compareMeasurements rank) (exchangeTape b a)
    ((swapGraph D a b).mp ⟨Derivation.conjunctionRight pair⟩) (compareShared rank b a r rb ra)
  have both := conjunctionAccept Y (swapExchange Y) (exchangeTape a b) p ((swapGraph Y a b).mpr q)
  obtain ⟨accept⟩ := conjunctionAccept (pairedExchange Y) (compareOptions C s) (exchangeTape a b)
    both ⟨Derivation.conjunctionRight g⟩
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight lawA)
    (Derivation.conjunctionIntroduction accept (Derivation.conjunctionRight calls))⟩

#print axioms exact_OpenForgetRankMeasuredPackedEdge
#print axioms exact_OpenInsertRankMeasuredPackedEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredPackedEdgeComparisonProof
