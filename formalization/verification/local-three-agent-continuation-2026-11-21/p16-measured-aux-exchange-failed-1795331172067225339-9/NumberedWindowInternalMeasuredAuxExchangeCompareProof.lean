module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCompositionCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalEqualityTestEvaluationProof (exactEqualityEvaluation)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalFactoredCoverChecks (exact_MeasureExchangeInvariance)
open NumberedWindowInternalAuxExchangeMemoGuardedTargets (accepted)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne vectorTwo)
open NumberedWindowInternalMeasuredAuxExchangeTargets

private theorem slotValue (M : Program 1) (i : Fin 2) (xs : List.Vector Nat 2) :
    evaluate (atSlot M i) xs = evaluate M (xs.get i ::ᵥ nil) := by
  change evaluate M (List.Vector.ofFn fun _ : Fin 1 => xs.get i) = _
  rw [vectorOne] <;> rfl

private theorem compareValue (M : Program 1) (a b : Nat) :
    evaluate (compareMeasurements M) (a ::ᵥ b ::ᵥ nil) =
      if evaluate M (a ::ᵥ nil) = evaluate M (b ::ᵥ nil) then 1 else 0 := by
  let xs := a ::ᵥ b ::ᵥ nil
  change evaluate equalityTest (List.Vector.ofFn
    (fun i => evaluate ((![atSlot M 0,atSlot M 1] : Fin 2 → Program 2) i) xs)) = _
  rw [vectorTwo]
  change evaluate equalityTest (evaluate (atSlot M 0) xs ::ᵥ evaluate (atSlot M 1) xs ::ᵥ nil) = _
  rw [slotValue,slotValue,exactEqualityEvaluation] <;> rfl

theorem calibration : ExactMeasuredExchangeCalibration := by
  intro s M X measure exchange a b
  have acceptedBase := exchange a b
  rw [vectorTwo] at acceptedBase ⊢
  change evaluate (measuredExchange M X) (a ::ᵥ b ::ᵥ nil) = _
  rw [measuredExchange,actualConjunctionEvaluation,acceptedBase,compareValue]
  cases bit : (bits s.equivalentHeads a b).1 with
  | false => simp [bit]
  | true =>
    have same := exact_MeasureExchangeInvariance M measure s.equivalentHeads a b bit
    simp [bit,same]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem slotForward (M : Program 1) (i : Fin 2) (out : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (unary M out (xs i)))) :
    Nonempty (Derivation body Γ (programGraph (atSlot M i) out xs)) := by
  apply compositionValue M (fun _ : Fin 1 => .projection i) out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem slotBackward (M : Program 1) (i : Fin 2) (out : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (atSlot M i) out xs))) :
    Nonempty (Derivation body Γ (unary M out (xs i))) := by
  apply compositionRecover M (fun _ : Fin 1 => .projection i) out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

theorem compareShared (M : Program 1) (a b m : OTerm α)
    (one : Nonempty (Derivation body Γ (unary M m a)))
    (two : Nonempty (Derivation body Γ (unary M m b))) :
    Nonempty (Derivation body Γ (accepted (compareMeasurements M) a b)) := by
  apply compositionValue equalityTest ![atSlot M 0,atSlot M 1] (suc z) ![a,b] ![m,m] (equalitySelf m)
  intro k
  exact Fin.cases (slotForward M 0 m ![a,b] one)
    (Fin.cases (slotForward M 1 m ![a,b] two) (fun j => Fin.elim0 j)) k

theorem compareCases (M : Program 1) (a b : OTerm α) (goal : Formula α)
    (compared : Nonempty (Derivation body Γ (accepted (compareMeasurements M) a b)))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (unary M m (a.relabel j))) →
      Nonempty (Derivation body Δ (unary M m (b.relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  apply programCompositionCases equalityTest ![atSlot M 0,atSlot M 1] (suc z) ![a,b] goal compared
  intro β j ys Δ hJ test components
  let inputs : Fin 2 → OTerm β := ![a.relabel j,b.relabel j]
  have first := components 0
  have second := components 1
  simp only [binaryInputsRename] at first second
  simp only [sucRelabel,zRelabel] at test
  obtain ⟨same⟩ := equalityOfAcceptance (ys 0) (ys 1) test
  have left := slotBackward M 0 (ys 0) inputs first
  have right := slotBackward M 1 (ys 1) inputs second
  exact use β j Δ (ys 0) hJ left (outputTransport M (ys 1) (ys 0) ![b.relabel j] ⟨symm same⟩ right)

end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
