module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveBooleanProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPositiveNormalization {n : Nat} (p : Program n) (xs : Fin n → OTerm α) (v : OTerm α)
    (h : D B Γ (programGraph (normalize p) (suc v) xs)) : D B Γ (programGraph (normalize p) (suc z) xs) := by
  let a := programGraph p (suc z) xs
  obtain ⟨h⟩ := h
  obtain ⟨yes⟩ := normalizeAccept (body := B) (Gamma := a :: Γ) p xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  have no := normalizeReject (body := B) (Gamma := a.not :: Γ) p xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨bad⟩ := valueUnique (normalize p) (suc v) z xs ⟨addHyp h a.not⟩ no
  exact ⟨disjunctionElimination (excludedMiddle a) (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply bad)))⟩

theorem exact_OpenPositiveConjunction {n : Nat} (p q : Program n) (xs : Fin n → OTerm α) (v : OTerm α)
    (h : D B Γ (programGraph (conjunction p q) (suc v) xs)) :
    D B Γ (programGraph (conjunction p q) (suc z) xs) := by
  let a := programGraph p (suc z) xs
  obtain ⟨h⟩ := h
  have left := normalizeAccept (body := B) (Gamma := a :: Γ) p xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  have right := successorBranchElim (normalize p) (constantZero n) (normalize q)
    (suc v) z xs left ⟨addHyp h a⟩
  obtain ⟨yes⟩ := successorBranchIntro (normalize p) (constantZero n) (normalize q)
    (suc z) z xs left (exact_OpenPositiveNormalization q xs v right)
  have no := normalizeReject (body := B) (Gamma := a.not :: Γ) p xs ⟨Derivation.hypothesis List.mem_cons_self⟩
  have lost := zeroBranchElim (normalize p) (constantZero n) (normalize q)
    (suc v) xs no ⟨addHyp h a.not⟩
  obtain ⟨bad⟩ := valueUnique (constantZero n) (suc v) z xs lost (zeroConstantValue xs)
  exact ⟨disjunctionElimination (excludedMiddle a) (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply bad)))⟩

theorem exact_OpenPositiveAuxShape (q v : OTerm α) (h : D B Γ (unary termShape (suc v) q)) :
    D B Γ (unary termShape (suc z) q) := by
  unfold unary termShape nodeGood at h ⊢
  exact exact_OpenPositiveConjunction _ _ ![q] v h

#print axioms exact_OpenPositiveNormalization
#print axioms exact_OpenPositiveConjunction
#print axioms exact_OpenPositiveAuxShape
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveBooleanProof
