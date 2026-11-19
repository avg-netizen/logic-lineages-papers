import LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverBranchProof

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverGrammarProof
open NumberedWindowSyntax NumberedWindowPrimaryCoverSyntax NumberedWindowPrimaryCoverTargets
open NumberedWindowPrimaryCoverLayerProof NumberedWindowPrimaryCoverSimpleProof
open NumberedWindowPrimaryCoverBranchProof

private theorem both (S : Spine.Signature) (K : List Ty) (m n : Nat) :
    (∀ Q, TermAt S K m n Q) ∧ (∀ qs, ArgsAt S K m n qs) := by
  induction n with
  | zero =>
    constructor
    · intro Q _ _ hn
      cases Q <;> simp only [termBounds] at hn <;> omega
    · intro qs _ _ hn
      cases qs with
      | nil => exact nilMem _ _ _ _
      | cons Q qs => simp only [argsBounds] at hn; omega
  | succ n ih =>
    obtain ⟨iq,ia⟩ := ih
    constructor
    · intro Q
      cases Q with
      | free σ x => exact freeCase
      | bound σ i => exact boundCase
      | lam σ Q => exact lamCase (iq Q)
      | bottom σ => exact bottomCase
      | ordinary f bs => exact ordinaryCase (ia bs)
      | numbered f τ k bs es => exact numberedCase (ia bs) (ia es)
      | auxApp σ τ Q A => exact auxCase (iq Q) (iq A)
    · intro qs
      cases qs with
      | nil => intro _ _ _; exact nilMem _ _ _ _
      | cons Q qs => exact argsConsCase (iq Q) (ia qs)

theorem term : TermGrammarCoverage := by
  intro S K C τ Q m n h hm hn
  exact (both S K m n).1 Q h.2 hm hn

theorem args : ArgsGrammarCoverage := by
  intro S K qs m n hs hf hm hn
  exact (both S K m n).2 qs ⟨hs,hf⟩ hm hn

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverGrammarProof
