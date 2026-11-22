module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdvanceWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

def AdvanceWindows (raw : Program 5) (least W : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty source hop target : OTerm α),
    Nonempty (Derivation body Γ ((selectedGraph raw least (suc target) ctx ty (suc source) hop).imp
      (windowAt W ctx ty source ⊓ windowAt W ctx ty target)))

/-- Finish accepts an empty path from any source to itself. Its source
guard therefore remains an explicit object assumption. -/
def ExactFinishWindow : Prop :=
  ∀ (raw : Program 5) (least W : Program 3), AdvanceWindows raw least W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty source cert target : OTerm α),
      Nonempty (Derivation body Γ ((windowAt W ctx ty source ⊓ finishAt raw least ctx ty source cert target).imp
        (windowAt W ctx ty target)))

/-- The original positive program requires a genuine first hop. The whole
winning ordered certificate guards both endpoints without a supplied parse. -/
def ExactPositiveWindows : Prop :=
  ∀ (raw : Program 5) (least W : Program 3), AdvanceWindows raw least W →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty source cert target : OTerm α),
      Nonempty (Derivation body Γ ((positiveAt raw least ctx ty source cert target).imp
        (windowAt W ctx ty source ⊓ windowAt W ctx ty target)))

def ExactPhysicalPositiveWindowsFromRetained : Prop :=
  ExactRetainedPredecessor →
    ∀ (C : Program 3) (X : Program 2) (W root other : Program 3) (syntaxProg : Program 1) (s : Settings)
      (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty source cert target : OTerm α),
      let raw := typedRaw5 root other W syntaxProg
      let least := packedLeastProgram C X W s
      Nonempty (Derivation body Γ ((positiveAt raw least ctx ty source cert target).imp
        (windowAt W ctx ty source ⊓ windowAt W ctx ty target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
