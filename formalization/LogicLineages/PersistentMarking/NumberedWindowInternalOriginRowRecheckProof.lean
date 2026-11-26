module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt reports)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectInsertedRowTargets
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalOriginRowRecheckTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
local notation "T" => OrdinaryArithmetic.Term
local notation "Pr" => fun (f : Formula α) => Nonempty (Derivation B Γ f)

private theorem leftReport (p : Program 1) (out x y : T α)
    (h : Pr (unary p out x)) : Pr (programGraph (liftLeft p) out ![x,y]) := by
  apply compositionValue p ![.projection 0] out ![x,y] ![x] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![x,y]

private theorem rightReport (p : Program 1) (out x y : T α)
    (h : Pr (unary p out y)) : Pr (programGraph (liftRight p) out ![x,y]) := by
  apply compositionValue p ![.projection 1] out ![x,y] ![y] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![x,y]

/-- Only the pool changes. The exact row and its original positive
certificate are carried unchanged. -/
theorem exact_OpenRecheckOriginRow : ExactOpenRecheckOriginRow := by
  intro r B α Γ removedOld removedSide row decodedOld decodedSide target dom cert old parsed mem
  let xs : Fin 2 → T α := ![removedSide,row]
  let side (p : Program 2) (out : T α) := Nonempty (Derivation B Γ (programGraph p out xs))
  obtain ⟨oldRow⟩ := old.original
  obtain ⟨envelope⟩ := exactOpenTriple B α Γ 4 row target dom cert
  have oldFields := Derivation.implicationElimination (Derivation.conjunctionLeft envelope)
    (Derivation.conjunctionLeft oldRow)
  have tag : side rowGuard oneTerm :=
    rightReport (guardAt 4) oneTerm removedSide row ⟨Derivation.conjunctionLeft oldFields⟩
  have f0 : side (rowField 0) target := rightReport (field 0) target removedSide row old.targetField
  have f1 : side (rowField 1) dom := rightReport (field 1) dom removedSide row old.dominatorField
  have f2 : side (rowField 2) cert := rightReport (field 2) cert removedSide row old.certificateField
  have parseSide : side parseRemoved (suc decodedSide) :=
    leftReport parser (suc decodedSide) removedSide row parsed
  have constOne : side (literal 2 1) oneTerm := by
    change Nonempty (Derivation B Γ (programGraph (literal 2 1) oneTerm xs))
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 2 1 xs
  have ready : side poolReady oneTerm := successorBranchIntro parseRemoved
    (constantZero 2) (literal 2 1) oneTerm decodedSide xs parseSide constOne
  have pool : side poolCode decodedSide := by
    apply compositionValue predecessor ![parseRemoved] decodedSide xs ![suc decodedSide]
      (predecessorSuccessor decodedSide)
    intro i
    obtain rfl := Fin.eq_zero i
    exact parseSide
  have member : side memberAt oneTerm := by
    apply compositionValue scratchMember ![poolCode,rowField 1] oneTerm xs ![decodedSide,dom] mem
    intro i
    exact Fin.cases pool (Fin.cases f1 (fun j => Fin.elim0 j)) i
  have positive : side (positiveAt r) oneTerm := by
    apply compositionValue r ![rowField 1,rowField 2,rowField 0] oneTerm xs ![dom,cert,target]
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight oldRow)⟩
    intro i
    exact Fin.cases f1 (Fin.cases f2 (Fin.cases f0 (fun j => Fin.elim0 j))) i
  let inner := conjunction memberAt (positiveAt r)
  let tails := conjunction poolReady inner
  exact conjunctionAccept rowGuard tails xs tag
    (conjunctionAccept poolReady inner xs ready
      (conjunctionAccept memberAt (positiveAt r) xs member positive))

#print axioms exact_OpenRecheckOriginRow

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowRecheckProof
