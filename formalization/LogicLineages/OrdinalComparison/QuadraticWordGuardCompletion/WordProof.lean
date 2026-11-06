module
public import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.ScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

private theorem shifted_value (A : Word) (x : Nat) (j a : Int)
    (hpos : 0 ≤ (rawQuadraticShift j (wordValue A x) : Int)+a) :
    (wordValue (A ++ [quadraticLetter j,shiftLetter a]) x : Int) =
      (rawQuadraticShift j (wordValue A x) : Int)+a := by
  rw [WordAlgebraProof.wordValue_append]
  change (((rawQuadraticShift j (wordValue A x) : Int)+a).toNat : Int) = _
  exact Int.toNat_of_nonneg hpos

theorem quadraticWordGuardCorrect : Targets.QuadraticWordGuardCorrect := by
  intro D A B hA hB j k a b x y hx hy
  have hAt := WordGuardCompletion.Proof.wordReachCorrect D A _ x hA
    ((Nat.le_max_left _ _).trans hx)
  have hBt := WordGuardCompletion.Proof.wordReachCorrect D B _ y hB
    ((Nat.le_max_right _ _).trans hy)
  have hg := quantitativeQuadraticGap j k (a.natAbs+b.natAbs)
    (wordValue A x) (wordValue B y) hAt.2 hBt.2
  have hs := shiftedQuadraticOrder j k a b (wordValue A x) (wordValue B y) hAt.2 hBt.2
  have hvL := shifted_value A x j a hs.1.le
  have hvR := shifted_value B y k b hs.2.1.le
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply (WordAlgebraProof.wordDomain_append A _ x).mpr
    exact ⟨hAt.1,hg.1,hs.1.le,trivial⟩
  · apply (WordAlgebraProof.wordDomain_append B _ y).mpr
    exact ⟨hBt.1,hg.2.1,hs.2.1.le,trivial⟩
  · have h := hs.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.1
    rw [←hvL,←hvR] at h
    exact_mod_cast h
  · have h := hs.2.2.2.2
    rw [←hvL,←hvR] at h
    exact_mod_cast h

end LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.Proof
