module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceNormalizationProof
  (normalizeAccept normalizeRecover normalizeReject)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalAdditionLawsProof (leftZero)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (applyUnary exactBody field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot witnessShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseRawTick (rootTest tagFiveTest rootCall)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Literal root tape. -/
abbrev rootTape (q payload r : OTerm α) : Fin 3 → OTerm α := ![q,rootWitnessTerm payload,r]

theorem zeroNotOne {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p z xs))) :
    Nonempty (Derivation body Γ (programGraph p (suc z) xs).not) := by
  obtain ⟨dp⟩ := hp
  obtain ⟨h⟩ := valueUnique p (suc z) z xs
    (show Nonempty (Derivation body (programGraph p (suc z) xs :: Γ)
      (programGraph p (suc z) xs)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    ⟨addHyp dp _⟩
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply h)⟩

theorem rejectLeft {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p z xs))) :
    Nonempty (Derivation body Γ (programGraph (conjunction p q) z xs)) :=
  zeroBranchIntro (normalize p) (constantZero n) (normalize q) z xs
    (normalizeReject p xs (zeroNotOne p xs hp)) (constantZeroValue xs)

theorem rejectRight {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p (suc z) xs)))
    (hq : Nonempty (Derivation body Γ (programGraph q z xs))) :
    Nonempty (Derivation body Γ (programGraph (conjunction p q) z xs)) :=
  successorBranchIntro (normalize p) (constantZero n) (normalize q) z z xs
    (normalizeAccept p xs hp) (normalizeReject q xs (zeroNotOne q xs hq))

theorem zeroBelowFive : Nonempty (Derivation body Γ (ltF (z : OTerm α) (numeral 5))) := by
  apply actualOriginalOrderIntroduction body α Γ z (numeral 5) (numeral 4)
  rw [onEquality]
  exact ⟨leftZero (suc (numeral 4))⟩

/-- The literal tag5 test rejects a literal root witness: its physical
head is zero, which the original equality test separates from five. -/
theorem tagFiveZero (q payload r : OTerm α) :
    Nonempty (Derivation body Γ (programGraph tagFiveTest z (rootTape q payload r))) := by
  let n : OTerm α := rootWitnessTerm payload
  let test : Program 1 := .composition equalityTest ![cellHead,literal 1 5]
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) (z : OTerm α) (rawCons payload z)
  have good : Nonempty (Derivation body Γ (programGraph cellGood (suc z) ![n])) :=
    ⟨Derivation.conjunctionLeft cell⟩
  have head : Nonempty (Derivation body Γ (programGraph cellHead z ![n])) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have five : Nonempty (Derivation body Γ (programGraph (literal 1 5) (numeral 5) ![n])) :=
    literalGraph 5 ![n]
  have differs : Nonempty (Derivation body Γ (programGraph test z ![n])) := by
    apply compositionValue equalityTest ![cellHead,literal 1 5] z ![n] ![z,numeral 5]
      (rejectForwardOrder z (numeral 5) zeroBelowFive)
    intro i
    exact Fin.cases head (Fin.cases five (fun l => Fin.elim0 l)) i
  have inner := rejectLeft test (applyUnary (exactBody 1) cellTail) ![n] differs
  have shape : Nonempty (Derivation body Γ (unary witnessShape z n)) :=
    rejectRight cellGood (conjunction test (applyUnary (exactBody 1) cellTail)) ![n] good inner
  exact onTape witnessShape 1 z (rootTape q payload r) shape

/-- The literal root test accepts, and field zero of the witness slot is
the payload. -/
theorem rootReports (q payload r : OTerm α) :
    Nonempty (Derivation body Γ (programGraph rootTest (suc z) (rootTape q payload r))) ∧
    Nonempty (Derivation body Γ (programGraph (frameSlot 0 1) payload (rootTape q payload r))) := by
  let n : OTerm α := rootWitnessTerm payload
  have tag : Nonempty (Derivation body Γ (unary (literal 1 0) (numeral 0) n)) :=
    literalGraph 0 ![n]
  have node := packedNode (literal 1 0) (numeral 0) [payload] tag
  exact ⟨onTape (nodeGood (literal 1 0) 1) 1 (suc z) (rootTape q payload r) node.1,
    onTape (field 0) 1 payload (rootTape q payload r) node.2.1⟩

private theorem rootInputs (q payload r : OTerm α) (i : Fin 3) :
    Nonempty (Derivation body Γ (programGraph
      ((![.projection 0,frameSlot 0 1,.projection 2] : Fin 3 → Program 3) i)
      ((![q,payload,r] : Fin 3 → OTerm α) i) (rootTape q payload r))) :=
  Fin.cases (projectionValue 0 (rootTape q payload r))
    (Fin.cases (rootReports q payload r).2
      (Fin.cases (projectionValue 2 (rootTape q payload r)) (fun e => Fin.elim0 e))) i

theorem rootCallAccept (p : Program 3) (q payload r : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph p (suc z) ![q,payload,r]))) :
    Nonempty (Derivation body Γ (programGraph (rootCall p) (suc z) (rootTape q payload r))) :=
  normalizeAccept (.composition p ![.projection 0,frameSlot 0 1,.projection 2])
    (rootTape q payload r)
    (compositionValue p ![.projection 0,frameSlot 0 1,.projection 2] (suc z)
      (rootTape q payload r) ![q,payload,r] h (rootInputs q payload r))

theorem rootCallRecover (p : Program 3) (q payload r : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (rootCall p) (suc z) (rootTape q payload r)))) :
    Nonempty (Derivation body Γ (programGraph p (suc z) ![q,payload,r])) :=
  compositionRecover p ![.projection 0,frameSlot 0 1,.projection 2] (suc z)
    (rootTape q payload r) ![q,payload,r]
    (normalizeRecover (.composition p ![.projection 0,frameSlot 0 1,.projection 2])
      (rootTape q payload r) h) (rootInputs q payload r)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
