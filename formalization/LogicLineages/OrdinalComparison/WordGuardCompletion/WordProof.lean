module
public import LogicLineages.OrdinalComparison.WordGuardCompletion.LetterProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordGuardCompletion.Proof
open PolynomialGraphCompletion

theorem wordTailCorrect : Targets.WordTailCorrect := by
  intro D w
  induction w with
  | nil =>
      intro t _ _
      simp [WordDomain,wordValue,wordOffset]
  | cons a w ih =>
      intro t ha ht
      have ha' : LetterAllowed D a := ha a List.mem_cons_self
      have hw : WordAllowed D w := fun b hb => ha b (List.mem_cons_of_mem a hb)
      change letterTail a+letterOffset a+wordTail w ≤ t at ht
      have hs := letterTailCorrect D a t ha' (by omega)
      have hn : wordTail w ≤ letterValue a t := by omega
      have hr := ih (letterValue a t) hw hn
      constructor
      · exact ⟨hs.1,hr.1⟩
      · change t ≤ wordValue w (letterValue a t)+(letterOffset a+wordOffset w)
        omega

theorem wordReachCorrect : Targets.WordReachCorrect := by
  intro D w K t hw ht
  unfold reachTail at ht
  have hs := wordTailCorrect D w t hw (by omega)
  exact ⟨hs.1,by omega⟩

theorem composedDomainCorrect : Targets.ComposedDomainCorrect := by
  intro D u v t hu hv ht
  have hs := wordReachCorrect D u (wordTail v) t hu ht
  have hr := wordTailCorrect D v (wordValue u t) hv hs.2
  exact ⟨hs.1,hr.1,(WordAlgebraProof.wordDomain_append u v t).mpr ⟨hs.1,hr.1⟩⟩

end LogicLineages.OrdinalComparison.WordGuardCompletion.Proof
