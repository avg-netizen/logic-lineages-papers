module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)

attribute [local irreducible] programGraph
variable {T : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenTypedAuxEdgeBase (B E : Program 4) (ctx ty q r : OTerm α)
    (held : D T Γ (acceptEdge (typedAuxEdgeGuard B E) ctx ty q r)) :
    D T Γ (acceptEdge B ctx ty q r) := by
  obtain ⟨parts⟩ := conjunctionRecover B (auxChildGuard E) ![ctx,ty,q,r] held
  exact ⟨Derivation.conjunctionLeft parts⟩

theorem exact_OpenTypedAuxEdgeNonAux (B E : Program 4) (ctx ty q r : OTerm α)
    (held : D T Γ (acceptEdge B ctx ty q r))
    (plain : D T Γ (unary termShape z q)) :
    D T Γ (acceptEdge (typedAuxEdgeGuard B E) ctx ty q r) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,q,r]
  have check := zeroBranchIntro (readSlot termShape 2) (constantOne 4) (validateAuxiliary E) (suc z) xs
    (exact_OpenEdgeSlotRead termShape 2 xs z plain) (oneConstantValue xs)
  exact conjunctionAccept B (auxChildGuard E) xs held check

private theorem chooseFn (E : Program 4) (xs : Fin 4 → OTerm α)
    (fn : D T Γ (programGraph (functionCase E) (suc z) xs)) :
    D T Γ (programGraph (chooseChild E) (suc z) xs) :=
  successorBranchIntro (normalize (functionCase E)) (argumentCase E) (constantOne 4) (suc z) z xs
    (normalizeAccept (functionCase E) xs fn) (oneConstantValue xs)

private theorem chooseArg (E : Program 4) (xs : Fin 4 → OTerm α)
    (arg : D T Γ (programGraph (argumentCase E) (suc z) xs)) :
    D T Γ (programGraph (chooseChild E) (suc z) xs) := by
  let F := programGraph (functionCase E) (suc z) xs
  obtain ⟨h⟩ := arg
  obtain ⟨fn⟩ := chooseFn (T := T) (Γ := F :: Γ) E xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  have no := normalizeReject (body := T) (Gamma := F.not :: Γ) (functionCase E) xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨other⟩ := zeroBranchIntro (normalize (functionCase E)) (argumentCase E) (constantOne 4) (suc z) xs
    no ⟨addHyp h F.not⟩
  exact ⟨disjunctionElimination (excludedMiddle F) (Derivation.implicationIntroduction fn)
    (Derivation.implicationIntroduction other)⟩

private theorem chooseFromReports (E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (reports : D T Γ (childAlternatives E ctx a b)) :
    D T Γ (programGraph (chooseChild E) (suc z) ![ctx,ty,a.term,b.term]) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
  let F := acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg
  let A := eqn a.fn b.fn ⊓ acceptEdge E ctx a.dom a.arg b.arg
  have p : Derivation T (F :: Γ) F := Derivation.hypothesis List.mem_cons_self
  have q : Derivation T (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨_,fl⟩ := termReports (body := T) (Γ := F :: Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,fr⟩ := termReports (body := T) (Γ := F :: Γ) b.dom b.cod b.fn b.arg
  obtain ⟨_,al⟩ := termReports (body := T) (Γ := A :: Γ) a.dom a.cod a.fn a.arg
  obtain ⟨_,ar⟩ := termReports (body := T) (Γ := A :: Γ) b.dom b.cod b.fn b.arg
  have left := (exact_OpenFunctionChildEdge E ctx ty a b).2 ⟨Derivation.conjunctionLeft p⟩
  have right := (exact_OpenArgumentChildEdge E ctx ty a b).2 ⟨Derivation.conjunctionRight q⟩
  have argEq := (exact_OpenEdgeFieldMatch xs 3 a.arg b.arg fl.2.2.2.1 fr.2.2.2.1).2
    ⟨Derivation.conjunctionRight p⟩
  have fnEq := (exact_OpenEdgeFieldMatch xs 2 a.fn b.fn al.2.2.1 ar.2.2.1).2 ⟨Derivation.conjunctionLeft q⟩
  obtain ⟨f⟩ := chooseFn E xs (conjunctionAccept (functionChildEdge E) (sameField 3) xs left argEq)
  obtain ⟨a⟩ := chooseArg E xs (conjunctionAccept (sameField 2) (argumentChildEdge E) xs fnEq right)
  obtain ⟨h⟩ := reports
  exact ⟨disjunctionElimination h (Derivation.implicationIntroduction f) (Derivation.implicationIntroduction a)⟩

/-- Reassemble the actual edge on literal auxiliary endpoints from the
real smaller typed edge and identical partner, checking the original
base guard and both original common type fields. -/
theorem exact_OpenTypedAuxEdgeIntro (B E : Program 4) (ctx ty : OTerm α) (a b : AuxRow α)
    (base : D T Γ (acceptEdge B ctx ty a.term b.term))
    (sameDom : D T Γ (eqn a.dom b.dom)) (sameCod : D T Γ (eqn a.cod b.cod))
    (child : D T Γ (childAlternatives E ctx a b)) :
    D T Γ (acceptEdge (typedAuxEdgeGuard B E) ctx ty a.term b.term) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,a.term,b.term]
  obtain ⟨left,fa⟩ := termReports (body := T) (Γ := Γ) a.dom a.cod a.fn a.arg
  obtain ⟨right,fb⟩ := termReports (body := T) (Γ := Γ) b.dom b.cod b.fn b.arg
  have d := (exact_OpenEdgeFieldMatch xs 0 a.dom b.dom fa.1 fb.1).2 sameDom
  have c := (exact_OpenEdgeFieldMatch xs 1 a.cod b.cod fa.2.1 fb.2.1).2 sameCod
  have src := exact_OpenEdgeSlotRead termShape 2 xs (suc z) left
  have dst := exact_OpenEdgeSlotRead termShape 3 xs (suc z) right
  have chosen := chooseFromReports E ctx ty a b child
  have r := conjunctionAccept (sameField 1) (chooseChild E) xs c chosen
  have lr := conjunctionAccept (sameField 0) (conjunction (sameField 1) (chooseChild E)) xs d r
  have shape := conjunctionAccept (readSlot termShape 3)
    (conjunction (sameField 0) (conjunction (sameField 1) (chooseChild E))) xs dst lr
  have accepted := successorBranchIntro (readSlot termShape 2) (constantOne 4) (validateAuxiliary E)
    (suc z) z xs src shape
  exact conjunctionAccept B (auxChildGuard E) xs base accepted

#print axioms exact_OpenTypedAuxEdgeBase
#print axioms exact_OpenTypedAuxEdgeNonAux
#print axioms exact_OpenTypedAuxEdgeIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
