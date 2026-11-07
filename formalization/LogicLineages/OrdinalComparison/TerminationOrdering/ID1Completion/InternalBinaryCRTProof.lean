module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalOrientedBezoutSyntaxProof InternalOrientedBezoutProof
open InternalBinaryCRT InternalBinaryCRTSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem solutionFromOriented (a b r s : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (of a b))) :
    Nonempty (Derivation body Gamma (solution (suc a) (suc b) r s)) := by
  apply orientedCases Gamma a b _ h
  intro β j Delta u v _ hc
  rw [solutionRename]
  simp only [sucRelabel]
  obtain ⟨hs⟩ := InternalBezoutCRTProof.actualCombination body β Delta
    (suc (a.relabel j)) (b.relabel j) u v (r.relabel j) (s.relabel j) hc
  exact ⟨solutionIntroduction _ _ _ _ _ hs⟩

theorem actualBinaryCRT : InternalBinaryCRTTargets.ActualBinaryCRT := by
  intro body α a b r s
  obtain ⟨ho⟩ := actualOrientedBezoutFromCoprimality body α a b
  let p := InternalBezoutExistenceTargets.coprime (suc a) (suc b)
  have hp : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  have hc := Derivation.implicationElimination (weakenClosed ho [p]) hp
  obtain ⟨hs⟩ := solutionFromOriented a b r s ⟨hc⟩
  exact ⟨Derivation.implicationIntroduction hs⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTProof
