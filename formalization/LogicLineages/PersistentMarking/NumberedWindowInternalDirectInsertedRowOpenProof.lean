module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRow
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt reports)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectInsertedRowTargets
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem leftReport (p : Program 1) (out x y : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (unary p out x))) :
    Nonempty (Derivation B Γ (programGraph (liftLeft p) out ![x,y])) := by
  apply compositionValue p ![.projection 0] out ![x,y] ![x] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![x,y]

private theorem rightReport (p : Program 1) (out x y : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (unary p out y))) :
    Nonempty (Derivation B Γ (programGraph (liftRight p) out ![x,y])) := by
  apply compositionValue p ![.projection 1] out ![x,y] ![y] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![x,y]

private theorem recoverRight (p : Program 1) (out x y : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (programGraph (liftRight p) out ![x,y]))) :
    Nonempty (Derivation B Γ (unary p out y)) := by
  apply compositionRecover p ![.projection 1] out ![x,y] ![y] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![x,y]

private theorem poolReport (removed row decoded : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation B Γ (unary parser (OrdinaryArithmetic.succTerm decoded) removed))) :
    Nonempty (Derivation B Γ (programGraph poolCode decoded ![removed,row])) := by
  let carried : Nonempty (Derivation B Γ (programGraph parseRemoved
      (OrdinaryArithmetic.succTerm decoded) ![removed,row])) :=
    leftReport parser _ removed row h
  apply compositionValue predecessor ![parseRemoved] decoded ![removed,row]
    ![OrdinaryArithmetic.succTerm decoded]
  · exact predecessorSuccessor decoded
  · intro i
    obtain rfl := Fin.eq_zero i
    exact carried

private theorem recoveredMembership (removed row decoded dom : OrdinaryArithmetic.Term α)
    (hit : Nonempty (Derivation B Γ (programGraph memberAt oneTerm ![removed,row])))
    (pool : Nonempty (Derivation B Γ (programGraph poolCode decoded ![removed,row])))
    (fieldAt : Nonempty (Derivation B Γ (programGraph (rowField 1) dom ![removed,row]))) :
    Nonempty (Derivation B Γ (programGraph scratchMember oneTerm ![decoded,dom])) := by
  apply compositionRecover scratchMember ![poolCode,rowField 1] oneTerm ![removed,row]
    ![decoded,dom] hit
  intro i
  exact Fin.cases pool (Fin.cases fieldAt (fun j => Fin.elim0 j)) i

private theorem recoveredPositive (r : Program 3) (removed row target dom cert : OrdinaryArithmetic.Term α)
    (hit : Nonempty (Derivation B Γ (programGraph (positiveAt r) oneTerm ![removed,row])))
    (f0 : Nonempty (Derivation B Γ (programGraph (rowField 0) target ![removed,row])))
    (f1 : Nonempty (Derivation B Γ (programGraph (rowField 1) dom ![removed,row])))
    (f2 : Nonempty (Derivation B Γ (programGraph (rowField 2) cert ![removed,row]))) :
    Nonempty (Derivation B Γ (programGraph r oneTerm ![dom,cert,target])) := by
  apply compositionRecover r ![rowField 1,rowField 2,rowField 0] oneTerm ![removed,row]
    ![dom,cert,target] hit
  intro i
  exact Fin.cases f1 (Fin.cases f2 (Fin.cases f0 (fun j => Fin.elim0 j))) i

theorem exactOpenInsertedRow : ExactOpenInsertedRow := by
  intro r B α Γ removed row decoded target dom cert pool f0 f1 f2 accepted
  let args : Fin 2 → OrdinaryArithmetic.Term α := ![removed,row]
  let inner := conjunction memberAt (positiveAt r)
  let tails := conjunction poolReady inner
  obtain ⟨outer⟩ := conjunctionRecover rowGuard tails args accepted
  obtain ⟨rest⟩ := conjunctionRecover poolReady inner args ⟨Derivation.conjunctionRight outer⟩
  obtain ⟨hits⟩ := conjunctionRecover memberAt (positiveAt r) args ⟨Derivation.conjunctionRight rest⟩
  obtain ⟨tag⟩ := recoverRight (guardAt 4) oneTerm removed row ⟨Derivation.conjunctionLeft outer⟩
  obtain ⟨q⟩ := exactOpenTriple B α Γ 4 row target dom cert
  obtain ⟨a⟩ := f0
  obtain ⟨b⟩ := f1
  obtain ⟨c⟩ := f2
  have ordered : Derivation B Γ (reports 4 row target dom cert) :=
    Derivation.conjunctionIntroduction tag
      (Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b c))
  have packed := Derivation.implicationElimination (Derivation.conjunctionRight q) ordered
  obtain ⟨m⟩ := recoveredMembership removed row decoded dom ⟨Derivation.conjunctionLeft hits⟩
    (poolReport removed row decoded pool) (rightReport (field 1) dom removed row ⟨b⟩)
  obtain ⟨p⟩ := recoveredPositive r removed row target dom cert ⟨Derivation.conjunctionRight hits⟩
    (rightReport (field 0) target removed row ⟨a⟩)
    (rightReport (field 1) dom removed row ⟨b⟩)
    (rightReport (field 2) cert removed row ⟨c⟩)
  exact ⟨Derivation.conjunctionIntroduction packed (Derivation.conjunctionIntroduction m p)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRow
