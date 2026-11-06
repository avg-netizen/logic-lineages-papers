module
public import LogicLineages.OrdinalComparison.RangePhiFactorization.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.WordProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

theorem predecessorHeadSyntax : Targets.PredecessorHeadSyntax := by
  intro D a ha _hr
  exact ⟨ha,rfl,rfl,rfl,rfl⟩

/-- Positive predecessor depth makes the natural iterate index an actual
successor, rather than relying on truncation at nonpositive signed depths. -/
private theorem iterate_factor (p q : Int) (t : Nat) (hq : 0 < q) (hp : p = q+1) :
    (Phi^[p.toNat]) t = Phi ((Phi^[q.toNat]) t) := by
  have hn : p.toNat = q.toNat+1 := by omega
  rw [hn,Function.iterate_succ_apply']

theorem headFactorization : Targets.HeadFactorization := by
  intro D a t ha hr ht
  have ha' := (predecessorHeadSyntax D a ha hr).1
  have hOrig := WordGuardCompletion.Proof.letterTailCorrect D a t ha
    ((Nat.le_max_left _ _).trans ht)
  have hPred := WordGuardCompletion.Proof.letterTailCorrect D (predecessorHead a) t ha'
    ((Nat.le_max_right _ _).trans ht)
  refine ⟨hOrig.1,hPred.1,?_⟩
  rcases a with ⟨tag,d,c,j⟩
  change tag = 2 ∨ tag = 3 at hr
  rcases hr with h2 | h3
  · subst tag
    change rawQuadraticShift j t = Phi (rawQuadraticShift (j-1) t)
    have hp : (0 : Int) < ((Phi t/2 : Nat) : Int)+(j-1)+1 := hPred.1
    unfold rawQuadraticShift
    apply iterate_factor _ _ t hp
    omega
  · subst tag
    change sourceSignedValue d c j t = Phi (sourceSignedValue d c (j-1) t)
    have hp : 0 < sourceSignedDepth d c (j-1) t := hPred.1.2
    unfold sourceSignedValue
    apply iterate_factor _ _ t hp
    unfold sourceSignedDepth
    omega

theorem word_allowed_append (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B) : WordAllowed D (A++B) := by
  intro a ha
  exact (List.mem_append.mp ha).elim (hA a) (hB a)

theorem singleton_allowed (D : Nat) (a : Letter) (ha : LetterAllowed D a) :
    WordAllowed D [a] := by
  intro b hb
  have h := List.mem_singleton.mp hb
  subst b
  exact ha

theorem factored_allowed (D : Nat) (a : Letter) (ha : LetterAllowed D a) (hr : RangeHead a) :
    WordAllowed D [predecessorHead a,phiLetter] := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact (predecessorHeadSyntax D a ha hr).1
  · have h := List.mem_singleton.mp hb
    subst b
    trivial

/-- Prefix calibration at the actual interior value. -/
theorem prefixFactorization (D : Nat) (A : Word) (a : Letter) (x : Nat)
    (hA : WordAllowed D A) (ha : LetterAllowed D a) (hr : RangeHead a)
    (hx : wordFactorTail A a ≤ x) :
    WordDomain (A++[a]) x ∧ WordDomain (A++[predecessorHead a,phiLetter]) x ∧
    wordValue (A++[a]) x = wordValue (A++[predecessorHead a,phiLetter]) x := by
  have hi := WordGuardCompletion.Proof.wordReachCorrect D A (factorTail a) x hA hx
  have hh := headFactorization D a (wordValue A x) ha hr hi.2
  refine ⟨(WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hi.1,hh.1,trivial⟩,
    (WordAlgebraProof.wordDomain_append A _ x).mpr ⟨hi.1,hh.2.1,trivial,trivial⟩,?_⟩
  rw [WordAlgebraProof.wordValue_append,WordAlgebraProof.wordValue_append]
  exact hh.2.2

end LogicLineages.OrdinalComparison.RangePhiFactorization.Proof
