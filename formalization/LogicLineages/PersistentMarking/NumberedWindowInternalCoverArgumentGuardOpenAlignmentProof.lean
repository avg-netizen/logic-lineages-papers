module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenBitsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTailProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairOrderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenAlignmentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue outputTransport)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (cellEquation zeroAccept)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellSuccessProof (cellToCons)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePairOrderProof (consTailDecrease)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentHead argumentTail tailMeasure)
open NumberedWindowInternalCoverArgumentMemoTailProof (actualArgumentTailLookup)
open NumberedWindowInternalCoverArgumentGuardOpenBitsProof (actualArgumentGuardBits)
open NumberedWindowInternalCoverArgumentGuardTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualArgumentGuardAlignment (G : Program 1) (prior old h a v : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (argumentRejectUpdate G) z ![prior,old,z,z])))
    (table : Nonempty (Derivation body Γ (tableAt (argumentRejectUpdate G) old prior)))
    (head : Nonempty (Derivation body Γ (unary cellHead h (suc prior))))
    (tail : Nonempty (Derivation body Γ (unary cellTail a (suc prior))))
    (row : Nonempty (Derivation body Γ (readRow (argumentRejectUpdate G) v a))) :
    Nonempty (Derivation body Γ (eqn (suc prior) (rawCons h a))) ∧
    Nonempty (Derivation body Γ (ltF a (suc prior))) ∧
    Nonempty (Derivation body Γ (unary G (suc z) h)) ∧
    Nonempty (Derivation body Γ (unary (argumentReject G) z a)) := by
  let raw := suc prior
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  let R := argumentRejectUpdate G
  obtain ⟨good,hd,tl⟩ := actualArgumentGuardBits G prior old actual
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have goodRaw : Nonempty (Derivation body Γ (unary cellGood (suc z) raw)) := by
    apply compositionRecover cellGood (fun _ : Fin 1 => currentKey) (suc z) xs ![raw] good
    intro i
    obtain rfl := Fin.eq_zero i
    exact key
  have pack := cellEquation raw h a goodRaw head tail
  have cert : Nonempty (Derivation body Γ (consGraph raw h a)) := by
    obtain ⟨u⟩ := goodRaw
    obtain ⟨y⟩ := head
    obtain ⟨t⟩ := tail
    exact cellToCons raw h a ⟨Derivation.conjunctionIntroduction u (Derivation.conjunctionIntroduction y t)⟩
  obtain ⟨order⟩ := closedApply (consTailDecrease body α raw h a) cert
  have early : Nonempty (Derivation body Γ (ltF a raw)) := ⟨Derivation.conjunctionRight order⟩
  have headReport : Nonempty (Derivation body Γ (programGraph argumentHead h xs)) :=
    unaryGraph cellHead currentKey h raw xs head key
  have headValid : Nonempty (Derivation body Γ (unary G (suc z) h)) := by
    apply compositionRecover G (fun _ : Fin 1 => argumentHead) (suc z) xs ![h] hd
    intro i
    obtain rfl := Fin.eq_zero i
    exact headReport
  have tailReport : Nonempty (Derivation body Γ (programGraph argumentTail a xs)) :=
    unaryGraph cellTail currentKey a raw xs tail key
  have looked := actualArgumentTailLookup R a v prior old tailReport early row table
  let Z := LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.zeroTest
  have test : Nonempty (Derivation body Γ (unary Z (suc z) v)) := by
    apply compositionRecover Z (fun _ : Fin 1 => tailMeasure) (suc z) xs ![v] tl
    intro i
    obtain rfl := Fin.eq_zero i
    exact looked
  have zero := zeroAccept v test
  have actualTail : Nonempty (Derivation body Γ (readRow R z a)) :=
    outputTransport (NumberedWindowInternalSparseFieldParser.scratchRow (ID1Completion.InternalAcceptance.constantZero 2) R)
      v z ![a,z,z] zero row
  exact ⟨pack,early,headValid,(projection R z a).mpr actualTail⟩

#print axioms actualArgumentGuardAlignment

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGuardOpenAlignmentProof
