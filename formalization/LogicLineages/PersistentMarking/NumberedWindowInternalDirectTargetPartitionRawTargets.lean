module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapCasesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape parsedAt payloadAt observePartition)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets scratchTargets)

def mapAt : Program 3 := .composition insertedTargets ![.projection 2]
def mapReady : Program 3 := branch mapAt (constantZero 3) (constantOne 3)
def mapPayload : Program 3 := .composition predecessor ![mapAt]
def allReady : Program 3 := conjunction (parsedAt 0) (conjunction (parsedAt 1) mapReady)
def decodeCall (test : Program 2) : Program 3 :=
  .composition (observePartition test) ![payloadAt 0,payloadAt 1,mapPayload]

/-- Raw tape order: original target, kept, inserted. -/
def rawTargetCheck (test : Program 2) : Program 3 := conjunction allReady (decodeCall test)

structure Reports (test : Program 2) (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (target kept inserted dt dk di projected joined : OTerm α) : Prop where
  targetReport : Nonempty (Derivation B Γ (unary parser (suc dt) target))
  keptReport : Nonempty (Derivation B Γ (unary parser (suc dk) kept))
  insertedReport : Nonempty (Derivation B Γ (unary parser (suc di) inserted))
  rawMapReport : Nonempty (Derivation B Γ (unary insertedTargets (suc projected) inserted))
  scratchMapReport : Nonempty (Derivation B Γ (unary scratchTargets (suc projected) di))
  appendReport : Nonempty (Derivation B Γ (programGraph append joined ![dk,projected]))
  observerReport : Nonempty (Derivation B Γ (programGraph test (suc z) ![dt,joined]))

/-- All graph reports use the same actual parsed raw tapes. No property of
the observer is assumed; in particular this is not permutation reflection. -/
def ExactOpenRawTargetCheck : Prop :=
  ∀ (test : Program 2) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (target kept inserted : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (rawTargetCheck test) (suc z)
      (sourceTape target kept inserted))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dt dk di projected joined : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Reports test B Δ (target.relabel j) (kept.relabel j) (inserted.relabel j)
        dt dk di projected joined →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
