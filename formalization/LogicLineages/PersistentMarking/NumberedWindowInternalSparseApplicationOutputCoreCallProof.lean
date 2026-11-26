module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreCallProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (predecessor equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (addressGraph)
open NumberedWindowInternalSparseApplicationOutputCore
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape seedGraph)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem selectGraph (least : Program 3) (out ctx dom cod fn arg y : OTerm α)
    (known : Nonempty (Derivation body Γ (programGraph least out ![ctx,cod,auxiliaryTerm dom cod fn arg]))) :
    Nonempty (Derivation body Γ
      (programGraph (selectedLeast least) out (objectTape ctx dom cod fn arg y))) := by
  let v := objectTape ctx dom cod fn arg y
  let components : Fin 3 → Program 6 := ![.projection 0,.projection 2,seed]
  let terms : Fin 3 → OTerm α := ![ctx,cod,auxiliaryTerm dom cod fn arg]
  apply compositionValue least components out v terms known
  intro i
  exact Fin.cases (projectionValue 0 v)
    (Fin.cases (projectionValue 2 v) (Fin.cases (seedGraph ctx dom cod fn arg y)
      (fun e => Fin.elim0 e))) i

private theorem classGraph (least : Program 3) (k : OTerm α) (v : Fin 6 → OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph (selectedLeast least) (suc k) v))) :
    Nonempty (Derivation body Γ (programGraph (selectedClass least) k v)) := by
  apply compositionValue predecessor (fun _ : Fin 1 => selectedLeast least) k v ![suc k]
    (predecessorSuccessor k)
  intro i
  obtain rfl := Fin.eq_zero i
  exact selected

private theorem packedGraph (least : Program 3) (k ctx dom cod fn arg y : OTerm α)
    (selected : Nonempty (Derivation body Γ
      (programGraph (selectedLeast least) (suc k) (objectTape ctx dom cod fn arg y)))) :
    Nonempty (Derivation body Γ
      (programGraph (outputAddress least) (addressTerm ctx cod k) (objectTape ctx dom cod fn arg y))) := by
  let v := objectTape ctx dom cod fn arg y
  let components : Fin 3 → Program 6 := ![.projection 0,.projection 2,selectedClass least]
  let terms : Fin 3 → OTerm α := ![ctx,cod,k]
  apply compositionValue addressEmitter components (addressTerm ctx cod k) v terms (addressGraph ctx cod k)
  intro i
  exact Fin.cases (projectionValue 0 v)
    (Fin.cases (projectionValue 2 v) (Fin.cases (classGraph least k v selected)
      (fun e => Fin.elim0 e))) i

theorem comparison (least : Program 3) (k ctx dom cod fn arg y : OTerm α)
    (selected : Nonempty (Derivation body Γ
      (programGraph (selectedLeast least) (suc k) (objectTape ctx dom cod fn arg y)))) :
    Nonempty (Derivation body Γ (programGraph (compareOutput least) (suc z)
      (objectTape ctx dom cod fn arg y))) ↔
      Nonempty (Derivation body Γ (eqn y (addressTerm ctx cod k))) := by
  let v := objectTape ctx dom cod fn arg y
  let g : Fin 2 → Program 6 := ![.projection 5,outputAddress least]
  let emitted := addressTerm ctx cod k
  let out : Fin 2 → OTerm α := ![y,emitted]
  have parts (i : Fin 2) : Nonempty (Derivation body Γ (programGraph (g i) (out i) v)) := by
    exact Fin.cases (projectionValue 5 v)
      (Fin.cases (packedGraph least k ctx dom cod fn arg y selected) (fun e => Fin.elim0 e)) i
  exact ⟨fun h => equalityOfAcceptance y emitted
      (compositionRecover equalityTest g (suc z) v out h parts),
    fun h => compositionValue equalityTest g (suc z) v out (equalityOfEqual y emitted h) parts⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreCallProof
