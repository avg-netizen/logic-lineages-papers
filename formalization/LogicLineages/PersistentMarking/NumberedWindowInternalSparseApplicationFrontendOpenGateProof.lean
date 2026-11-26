module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenGateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowGuardedGraphTargets (atSlot)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood arrowGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseApplicationFrontend
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotIntro slotRead)

attribute [local irreducible] programGraph

abbrev args {α : Type} (f u y : OTerm α) : Fin 3 → OTerm α := ![f,u,y]

abbrev G (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p : Program 3) (xs : Fin 3 → OTerm α) : Prop :=
  Nonempty (Derivation body Γ (programGraph p (suc z) xs))

structure Pieces (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (least : Program 3) (xs : Fin 3 → OTerm α) : Prop where
  fShape : G body Γ (atSlot addressGood 0) xs
  uShape : G body Γ (atSlot addressGood 1) xs
  fArrow : G body Γ (atSlot arrowGood 0) xs
  ctxEq : G body Γ sameContext xs
  domEq : G body Γ domainAgreement xs
  output : G body Γ (callOutput least) xs

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem readCore (least : Program 3) (xs : Fin 3 → OTerm α)
    (ok : G body Γ (applicationCore least) xs) : Pieces body Γ least xs := by
  let tail1 := conjunction domainAgreement (callOutput least)
  let tail2 := conjunction sameContext tail1
  let tail3 := conjunction (atSlot arrowGood 0) tail2
  let tail4 := conjunction (atSlot addressGood 1) tail3
  obtain ⟨p1⟩ := conjunctionRecover (atSlot addressGood 0) tail4 xs ok
  obtain ⟨p2⟩ := conjunctionRecover (atSlot addressGood 1) tail3 xs ⟨Derivation.conjunctionRight p1⟩
  obtain ⟨p3⟩ := conjunctionRecover (atSlot arrowGood 0) tail2 xs ⟨Derivation.conjunctionRight p2⟩
  obtain ⟨p4⟩ := conjunctionRecover sameContext tail1 xs ⟨Derivation.conjunctionRight p3⟩
  obtain ⟨p5⟩ := conjunctionRecover domainAgreement (callOutput least) xs ⟨Derivation.conjunctionRight p4⟩
  exact ⟨⟨Derivation.conjunctionLeft p1⟩,⟨Derivation.conjunctionLeft p2⟩,⟨Derivation.conjunctionLeft p3⟩,
    ⟨Derivation.conjunctionLeft p4⟩,⟨Derivation.conjunctionLeft p5⟩,⟨Derivation.conjunctionRight p5⟩⟩

theorem makeCore (least : Program 3) (xs : Fin 3 → OTerm α)
    (parts : Pieces body Γ least xs) : G body Γ (applicationCore least) xs := by
  let tail1 := conjunction domainAgreement (callOutput least)
  let tail2 := conjunction sameContext tail1
  let tail3 := conjunction (atSlot arrowGood 0) tail2
  let tail4 := conjunction (atSlot addressGood 1) tail3
  have p1 := conjunctionAccept domainAgreement (callOutput least) xs parts.domEq parts.output
  have p2 := conjunctionAccept sameContext tail1 xs parts.ctxEq p1
  have p3 := conjunctionAccept (atSlot arrowGood 0) tail2 xs parts.fArrow p2
  have p4 := conjunctionAccept (atSlot addressGood 1) tail3 xs parts.uShape p3
  exact conjunctionAccept (atSlot addressGood 0) tail4 xs parts.fShape p4

theorem readGuard (i : Program 1) (least : Program 3) (f u y : OTerm α)
    (h : G body Γ (applicationGuard i least) (args f u y)) :
    Nonempty (Derivation body Γ (unary i (suc z) f)) ∧
    Nonempty (Derivation body Γ (unary i (suc z) u)) ∧
    G body Γ (applicationCore least) (args f u y) := by
  let xs := args f u y
  let core := applicationCore least
  obtain ⟨outer⟩ := conjunctionRecover (atSlot i 0) (conjunction (atSlot i 1) core) xs h
  obtain ⟨inner⟩ := conjunctionRecover (atSlot i 1) core xs ⟨Derivation.conjunctionRight outer⟩
  exact ⟨slotRead i 0 (suc z) xs ⟨Derivation.conjunctionLeft outer⟩,
    slotRead i 1 (suc z) xs ⟨Derivation.conjunctionLeft inner⟩,⟨Derivation.conjunctionRight inner⟩⟩

theorem makeGuard (i : Program 1) (least : Program 3) (f u y : OTerm α)
    (left : Nonempty (Derivation body Γ (unary i (suc z) f)))
    (right : Nonempty (Derivation body Γ (unary i (suc z) u)))
    (coreOk : G body Γ (applicationCore least) (args f u y)) :
    G body Γ (applicationGuard i least) (args f u y) := by
  let xs := args f u y
  let core := applicationCore least
  have inner := conjunctionAccept (atSlot i 1) core xs (slotIntro i 1 (suc z) xs right) coreOk
  exact conjunctionAccept (atSlot i 0) (conjunction (atSlot i 1) core) xs
    (slotIntro i 0 (suc z) xs left) inner

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenGateProof
