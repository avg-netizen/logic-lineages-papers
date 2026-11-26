module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendListProof (appendZeroValue)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique headTransport)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalLiteralCountMembershipChecks (exact_OpenLiteralCountMembershipForward)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalOriginBothRemovedNonemptyTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeTwo (a b : OTerm α) :
    (![a,b] : Fin 2 → OTerm α) = Fin.cons a (Fin.cons b Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem joinNil (left right joined : OTerm α) (eL : D B Γ (eqn left z))
    (eR : D B Γ (eqn right z)) (ran : D B Γ (appendGraph joined left right)) :
    D B Γ (eqn joined z) := by
  have moved : D B Γ (appendGraph joined z z) := by
    unfold appendGraph programGraph at ran ⊢
    apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula append)
      joined ![left,right] ![z,z] _ ran
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change D B Γ (equal left z)
      rw [equalEqn]
      exact eL
    · obtain rfl := Fin.eq_zero j
      change D B Γ (equal right z)
      rw [equalEqn]
      exact eR
  have vacant : D B Γ (appendGraph z z z) := by
    simp only [appendGraph,tapeTwo]
    exact appendZeroValue (z : OTerm α)
  exact valueUnique append joined z ![z,z] moved vacant

private theorem emptyContradiction (head : OTerm α) (hit : D B Γ (memberGraph z head)) :
    D B Γ (⊥ : Formula α) := by
  have bad := nilRecover memberBase memberStep (suc z) ![head] hit
  have zero : D B Γ (programGraph memberBase z ![head]) := constantZeroValue ![head]
  obtain ⟨impossible⟩ := valueUnique memberBase (suc z) z ![head] bad zero
  exact ⟨sucNeZeroApply impossible⟩

/-- If both sides were physically nil, transport the old real head's
membership to that actual empty append; its original graph rejects. -/
theorem exact_OpenOriginBothRemovedNotNil : ExactOpenOriginBothRemovedNotNil := by
  intro B α Γ removed head tail left right joined cell app count
  let H := eqn left z ⊓ eqn right z
  let Δ := H :: Γ
  have hh : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  have empty := joinNil left right joined ⟨Derivation.conjunctionLeft hh⟩
    ⟨Derivation.conjunctionRight hh⟩ (withHyp app H)
  have member : D B Δ (memberGraph removed head) :=
    headMember removed head tail head (withHyp cell H)
      ⟨ID1Completion.InternalTagArithmeticSupportProof.refl head⟩
  have joinedHit := exact_OpenLiteralCountMembershipForward B α Δ removed joined head
    (withHyp count H) member
  have emptyHit := headTransport scratchMember (suc z) joined z ![head] empty joinedHit
  obtain ⟨bad⟩ := emptyContradiction head emptyHit
  exact ⟨Derivation.implicationIntroduction bad⟩

#print axioms exact_OpenOriginBothRemovedNotNil

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyProof
