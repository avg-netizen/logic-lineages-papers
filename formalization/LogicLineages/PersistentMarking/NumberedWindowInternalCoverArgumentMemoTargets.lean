module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalEqualityTest (subtract)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ArgsMeasureCalibrated)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)

/-- One new physical argument-only memo. The original term measure is
selected separately, not read from the argument column of this memo. -/
def argumentHead : Program 4 := unaryAfter cellHead currentKey
def argumentTail : Program 4 := unaryAfter cellTail currentKey
def argumentCell : Program 4 := unaryAfter cellGood currentKey
def tailOffset : Program 4 := binaryAfter subtract argumentTail (.projection 0)
def tailMeasure : Program 4 := binaryAfter lookup tailOffset (.projection 1)
def headMeasure (F : Program 1) : Program 4 := unaryAfter F argumentHead

def argumentUpdate (F : Program 1) : Program 4 :=
  branch argumentCell (constantZero 4) (binaryAfter chosenCombine (headMeasure F) tailMeasure)

abbrev argumentMeasure (F : Program 1) : Program 1 := selectedMeasure (argumentUpdate F)

def ExactCoverArgumentMemo : Prop :=
  ∀ F : Program 1, TermMeasureCalibrated F → ArgsMeasureCalibrated (argumentMeasure F)

/-- Real open selected child reports for the original literal cons and
exact output of this selected physical traversal; the nil case is separate. -/
def ExactOpenCoverArgumentMemoCons : Prop :=
  ∀ (F : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (head tail out : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary (argumentMeasure F) out (rawCons head tail))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (mh mt : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary F mh (head.relabel j))) →
      Nonempty (Derivation body Δ (unary (argumentMeasure F) mt (tail.relabel j))) →
      Nonempty (Derivation body Δ (programGraph chosenCombine (out.relabel j) ![mh,mt])) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTargets
