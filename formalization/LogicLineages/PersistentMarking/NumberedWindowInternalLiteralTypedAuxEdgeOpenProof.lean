module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

attribute [local irreducible] programGraph
variable {T : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def childAlternatives (E : Program 4) (ctx : OTerm α) (a b : AuxRow α) : Formula α :=
  (acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg) ⊔
    (eqn a.fn b.fn ⊓ acceptEdge E ctx a.dom a.arg b.arg)

private theorem fnReports (E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (held : D T Γ (programGraph (functionCase E) (suc z) ![ctx,ty,a.term,b.term])) :
    D T Γ (childAlternatives E ctx a b) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
  obtain ⟨f⟩ := conjunctionRecover (functionChildEdge E) (sameField 3) xs held
  obtain ⟨_,fa⟩ := termReports (body := T) (Γ := Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,fb⟩ := termReports (body := T) (Γ := Γ) b.dom b.cod b.fn b.arg
  obtain ⟨call⟩ := (exact_OpenFunctionChildEdge E ctx ty a b).1 ⟨Derivation.conjunctionLeft f⟩
  obtain ⟨same⟩ := (exact_OpenEdgeFieldMatch xs 3 a.arg b.arg fa.2.2.2.1 fb.2.2.2.1).1
    ⟨Derivation.conjunctionRight f⟩
  exact ⟨orLeft (Derivation.conjunctionIntroduction call same)⟩

private theorem argReports (E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (held : D T Γ (programGraph (argumentCase E) (suc z) ![ctx,ty,a.term,b.term])) :
    D T Γ (childAlternatives E ctx a b) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
  obtain ⟨r⟩ := conjunctionRecover (sameField 2) (argumentChildEdge E) xs held
  obtain ⟨_,fa⟩ := termReports (body := T) (Γ := Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,fb⟩ := termReports (body := T) (Γ := Γ) b.dom b.cod b.fn b.arg
  obtain ⟨same⟩ := (exact_OpenEdgeFieldMatch xs 2 a.fn b.fn fa.2.2.1 fb.2.2.1).1 ⟨Derivation.conjunctionLeft r⟩
  obtain ⟨call⟩ := (exact_OpenArgumentChildEdge E ctx ty a b).1 ⟨Derivation.conjunctionRight r⟩
  exact ⟨orRight (Derivation.conjunctionIntroduction same call)⟩

private theorem childCases (E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (held : D T Γ (programGraph (chooseChild E) (suc z) ![ctx,ty,a.term,b.term])) :
    D T Γ (childAlternatives E ctx a b) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
  let F := programGraph (functionCase E) (suc z) xs
  obtain ⟨yes⟩ := fnReports (T := T) (Γ := F :: Γ) E ctx ty a b ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨held⟩ := held
  have zero := normalizeReject (body := T) (functionCase E) xs
    (Gamma := F.not :: Γ) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have arg := zeroBranchElim (normalize (functionCase E)) (argumentCase E) (constantOne 4)
    (suc z) xs zero ⟨addHyp held F.not⟩
  obtain ⟨no⟩ := argReports E ctx ty a b arg
  exact ⟨disjunctionElimination (excludedMiddle F) (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction no)⟩

/-- The physically typed auxiliary guard can be eliminated in open
contexts. Recover the exact shared type fields and either an actual
function edge with unchanged argument or an actual argument edge
with unchanged function. No extensional equality of graphs is used. -/
theorem exact_OpenTypedAuxEdgeRows (B E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (held : D T Γ (acceptEdge (typedAuxEdgeGuard B E) ctx ty a.term b.term)) :
    D T Γ (eqn a.dom b.dom ⊓ (eqn a.cod b.cod ⊓ childAlternatives E ctx a b)) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
  obtain ⟨yes,fa⟩ := termReports (body := T) (Γ := Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,fb⟩ := termReports (body := T) (Γ := Γ) b.dom b.cod b.fn b.arg
  obtain ⟨outer⟩ := conjunctionRecover B (auxChildGuard E) xs held
  have shape := exact_OpenEdgeSlotRead termShape 2 xs (suc z) yes
  have known := successorBranchElim (readSlot termShape 2) (constantOne 4)
    (validateAuxiliary E) (suc z) z xs shape ⟨Derivation.conjunctionRight outer⟩
  obtain ⟨calls⟩ := conjunctionRecover (readSlot termShape 3)
    (conjunction (sameField 0) (conjunction (sameField 1) (chooseChild E))) xs known
  obtain ⟨fields⟩ := conjunctionRecover (sameField 0)
    (conjunction (sameField 1) (chooseChild E)) xs ⟨Derivation.conjunctionRight calls⟩
  obtain ⟨choices⟩ := conjunctionRecover (sameField 1) (chooseChild E) xs ⟨Derivation.conjunctionRight fields⟩
  obtain ⟨dom⟩ := (exact_OpenEdgeFieldMatch xs 0 a.dom b.dom fa.1 fb.1).1 ⟨Derivation.conjunctionLeft fields⟩
  obtain ⟨cod⟩ := (exact_OpenEdgeFieldMatch xs 1 a.cod b.cod fa.2.1 fb.2.1).1 ⟨Derivation.conjunctionLeft choices⟩
  obtain ⟨move⟩ := childCases E ctx ty a b ⟨Derivation.conjunctionRight choices⟩
  exact ⟨Derivation.conjunctionIntroduction dom (Derivation.conjunctionIntroduction cod move)⟩

#print axioms exact_OpenTypedAuxEdgeRows
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeOpenProof
