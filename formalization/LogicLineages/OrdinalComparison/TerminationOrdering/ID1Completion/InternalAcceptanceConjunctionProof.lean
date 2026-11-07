module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open InternalAcceptance InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof InternalBetaTotalityProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem constantZeroValue {n : Nat} (xs : Fin n → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (constantZero n) z xs)) := by
  apply compositionValue .zero Fin.elim0 z xs Fin.elim0 (zeroValue _)
  intro i
  exact Fin.elim0 i

theorem conjunctionAccept {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p (suc z) xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q (suc z) xs))) :
    Nonempty (Derivation body Gamma (programGraph (conjunction p q) (suc z) xs)) :=
  successorBranchIntro (normalize p) (constantZero n) (normalize q) (suc z) z xs
    (normalizeAccept p xs hp) (normalizeAccept q xs hq)

theorem conjunctionRecover {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph (conjunction p q) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      (programGraph p (suc z) xs ⊓ programGraph q (suc z) xs)) := by
  let P := programGraph p (suc z) xs
  let Q := programGraph q (suc z) xs
  obtain ⟨hw⟩ := hw
  have hy : Nonempty (Derivation body (P :: Gamma) (P ⊓ Q)) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hnq := successorBranchElim (normalize p) (constantZero n) (normalize q)
      (suc z) z xs (normalizeAccept p xs hp) ⟨addHyp hw P⟩
    obtain ⟨hq⟩ := normalizeRecover q xs hnq
    exact ⟨Derivation.conjunctionIntroduction (Derivation.hypothesis List.mem_cons_self) hq⟩
  have hn : Nonempty (Derivation body (P.not :: Gamma) (P ⊓ Q)) := by
    have hp : Nonempty (Derivation body (P.not :: Gamma) P.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := zeroBranchElim (normalize p) (constantZero n) (normalize q)
      (suc z) xs (normalizeReject p xs hp) ⟨addHyp hw P.not⟩
    obtain ⟨he⟩ := valueUnique (constantZero n) (suc z) z xs hz (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩

theorem actualOriginalConjunctionAcceptance : InternalAcceptanceTargets.ActualOriginalConjunctionAcceptance := by
  intro body n p q α xs
  let g := programGraph (conjunction p q) (suc z) xs
  let s := programGraph p (suc z) xs ⊓ programGraph q (suc z) xs
  obtain ⟨hf⟩ := conjunctionRecover (body := body) (Gamma := [g]) p q xs
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := conjunctionAccept (body := body) (Gamma := [s]) p q xs
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
