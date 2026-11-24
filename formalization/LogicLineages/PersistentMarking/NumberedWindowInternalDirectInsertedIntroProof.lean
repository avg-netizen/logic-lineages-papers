module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue equalEqn)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalRawListRecursionProof (consValue)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt reports tripleTerm)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectInsertedRowTargets
open NumberedWindowInternalDirectInsertedScanTargets
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
abbrev D (p : Formula α) := Nonempty (Derivation B Γ p)

private theorem readPool (raw other decoded : OTerm α)
    (good : D (B := B) (Γ := Γ) (unary parser (suc decoded) raw)) :
    D (B := B) (Γ := Γ) (programGraph poolReady (suc z) ![raw,other]) ∧
      D (B := B) (Γ := Γ) (programGraph poolCode decoded ![raw,other]) := by
  let tape : Fin 2 → OTerm α := ![raw,other]
  have call : D (B := B) (Γ := Γ) (programGraph parseRemoved (suc decoded) tape) := by
    apply compositionValue parser ![.projection 0] (suc decoded) tape ![raw] good
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 0 tape
  constructor
  · exact successorBranchIntro parseRemoved (constantZero 2) _ (suc z) decoded tape call (literalGraph 1 tape)
  · apply compositionValue predecessor ![parseRemoved] decoded tape ![suc decoded] (predecessorSuccessor decoded)
    intro k
    obtain rfl := Fin.eq_zero k
    exact call

private theorem readRow (p : Program 1) (removed row out : OTerm α)
    (read : D (B := B) (Γ := Γ) (unary p out row)) :
    D (B := B) (Γ := Γ) (programGraph (liftRight p) out ![removed,row]) := by
  apply compositionValue p ![.projection 1] out ![removed,row] ![row] read
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue 1 ![removed,row]

/-- The actual tag-4 row is accepted, with unchanged removed tape and
unchanged scalar certificate, when its dominator occurs in the decoded
tape and the actual positive code accepts. -/
theorem exact_OriginalInsertedRowIntro (r : Program 3)
    (removed decoded target dom cert : OTerm α)
    (pool : D (B := B) (Γ := Γ) (unary parser (suc decoded) removed))
    (member : D (B := B) (Γ := Γ) (memberGraph decoded dom))
    (edge : D (B := B) (Γ := Γ) (programGraph r (suc z) ![dom,cert,target])) :
    D (B := B) (Γ := Γ) (rowAccept r (tripleTerm 4 target dom cert) removed) := by
  let row := tripleTerm 4 target dom cert
  let args : Fin 2 → OTerm α := ![removed,row]
  obtain ⟨ready,code⟩ := readPool removed row decoded pool
  obtain ⟨both⟩ := exactOpenTriple B α Γ 4 row target dom cert
  have reflRow : Derivation B Γ (equal row (tripleTerm 4 target dom cert)) := by
    rw [equalEqn]
    exact refl row
  have seen : Derivation B Γ (reports 4 row target dom cert) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft both) reflRow
  have guard : D (B := B) (Γ := Γ) (programGraph rowGuard (suc z) args) :=
    readRow (guardAt 4) removed row _ ⟨Derivation.conjunctionLeft seen⟩
  have f0 := readRow (field 0) removed row target ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight seen)⟩
  have f1 := readRow (field 1) removed row dom ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight seen))⟩
  have f2 := readRow (field 2) removed row cert ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight seen))⟩
  have m : D (B := B) (Γ := Γ) (programGraph memberAt (suc z) args) := by
    apply compositionValue scratchMember ![poolCode,rowField 1] (suc z) args ![decoded,dom] member
    intro k
    exact Fin.cases code (Fin.cases f1 (fun v => Fin.elim0 v)) k
  have e : D (B := B) (Γ := Γ) (programGraph (positiveAt r) (suc z) args) := by
    apply compositionValue r ![rowField 1,rowField 2,rowField 0] (suc z) args ![dom,cert,target] edge
    intro k
    exact Fin.cases f1 (Fin.cases f2 (Fin.cases f0 (fun v => Fin.elim0 v))) k
  exact conjunctionAccept rowGuard (conjunction poolReady (conjunction memberAt (positiveAt r))) args guard
    (conjunctionAccept poolReady (conjunction memberAt (positiveAt r)) args ready
      (conjunctionAccept memberAt (positiveAt r) args m e))

theorem exact_OriginalScanConsIntro (r : Program 3) (code row tail removed : OTerm α)
    (cons : D (B := B) (Γ := Γ) (consGraph code row tail))
    (head : D (B := B) (Γ := Γ) (rowAccept r row removed))
    (next : D (B := B) (Γ := Γ) (loopAccept r tail removed)) :
    D (B := B) (Γ := Γ) (loopAccept r code removed) := by
  let args : Fin 3 → OTerm α := Fin.cons row (Fin.cons (suc z) ![removed])
  have headAt : D (B := B) (Γ := Γ) (programGraph (rowAt r) (suc z) args) := by
    apply compositionValue (insertedRow r) ![.projection 2,.projection 0]
      (suc z) args ![removed,row] head
    intro k
    exact Fin.cases (projectionValue 2 args)
      (Fin.cases (projectionValue 0 args) (fun v => Fin.elim0 v)) k
  exact consValue scanBase (scanStep r) code row tail (suc z) (suc z) ![removed] cons next
    (conjunctionAccept (rowAt r) (.projection 1) args headAt (projectionValue 1 args))

theorem exact_OriginalRawScanIntro (r : Program 3) (inserted removed decoded : OTerm α)
    (parsed : D (B := B) (Γ := Γ) (unary parser (suc decoded) inserted))
    (loop : D (B := B) (Γ := Γ) (loopAccept r decoded removed)) :
    D (B := B) (Γ := Γ) (programGraph (scan r) (suc z) ![inserted,removed]) := by
  let args : Fin 2 → OTerm α := ![inserted,removed]
  obtain ⟨ready,payload⟩ := readPool inserted removed decoded parsed
  have result : D (B := B) (Γ := Γ) (programGraph (scanAt r) (suc z) args) := by
    apply compositionValue (scanLoop r) ![poolCode,.projection 1] (suc z) args (Fin.cons decoded ![removed]) loop
    intro k
    exact Fin.cases payload (Fin.cases (projectionValue 1 args) (fun v => Fin.elim0 v)) k
  exact conjunctionAccept poolReady (scanAt r) args ready result

#print axioms exact_OriginalInsertedRowIntro
#print axioms exact_OriginalScanConsIntro
#print axioms exact_OriginalRawScanIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedIntroProof
