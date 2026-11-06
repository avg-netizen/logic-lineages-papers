module
public import LogicLineages.OrdinalComparison.RangePhiFactorization.ContextProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem phiHeadCancellation : Targets.PhiHeadCancellation := by
  intro D A B a hA hB ha hr x y hx hy
  have hAt := WordGuardCompletion.Proof.wordTailCorrect D A x hA ((Nat.le_max_left _ _).trans hx)
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B (factorTail a) y hB
    ((Nat.le_max_right _ _).trans hy)
  have hh := headFactorization D a (wordValue B y) ha hr hBt.2
  have hPred := (predecessorHeadSyntax D a ha hr).1
  have hleft : wordValue (A++[phiLetter]) x = Phi (wordValue A x) := by
    rw [WordAlgebraProof.wordValue_append]
    rfl
  have hright : wordValue (B++[a]) y = Phi (wordValue (B++[predecessorHead a]) y) := by
    rw [WordAlgebraProof.wordValue_append,WordAlgebraProof.wordValue_append]
    exact hh.2.2
  refine ⟨(WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hAt.1,trivial,trivial⟩,
    (WordAlgebraProof.wordDomain_append B _ y).mpr ⟨hBt.1,hh.1,trivial⟩,
    word_allowed_append D B _ hB (singleton_allowed D _ hPred),
    (WordAlgebraProof.wordDomain_append B _ y).mpr ⟨hBt.1,hh.2.1,trivial⟩,?_,?_,?_⟩
  · rw [hleft,hright]
    exact Phi_strictMono.lt_iff_lt
  · rw [hleft,hright]
    exact Phi_strictMono.injective.eq_iff
  · rw [hleft,hright]
    exact Phi_strictMono.le_iff_le

end LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
