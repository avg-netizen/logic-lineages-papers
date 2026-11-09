module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearProof
open BlockRows TiedLinear

def tokenVariables : Token → List Nat
  | .parameter t => t.variables
  | .occurrence s => [s.name]

theorem literalTokenRoundTrip : TiedLinearTargets.LiteralTokenRoundTrip := by
  intro table x t ht
  by_cases h : t = rawToken x
  · subst t
    simp [tokenName, tokenOfName]
  · rw [tokenName, if_neg h, tokenOfName, if_neg (by omega)]
    simp only [Nat.add_sub_cancel, List.getElem?_idxOf ht, Option.getD_some]

theorem token_name_zero (table : List Token) (x : Nat) (t : Token) :
    tokenName table x t = 0 ↔ t = rawToken x := by
  by_cases h : t = rawToken x <;> simp [tokenName, h]

theorem parameter_token (table : List Token) (x : Nat) (ν : Nat → Nat) (t : Token)
    (ht : t ∈ table) :
    parameterValuation table x ν (tokenName table x t) = t.value ν := by
  simp only [parameterValuation, literalTokenRoundTrip table x t ht]

theorem token_update (t : Token) (x n : Nat) (ν : Nat → Nat)
    (hx : x ∉ tokenVariables t) : t.value (Function.update ν x n) = t.value ν := by
  cases t with
  | parameter t => exact WindowProof.term_update t x n ν hx
  | occurrence s =>
    apply WindowProof.term_update s.term x n ν
    intro hm
    exact hx (List.mem_singleton.mpr ((BlockRowsProof.original_summand_variables s x).mp hm))

theorem parameter_token_updated (table : List Token) (x : Nat) (ν : Nat → Nat)
    (n : Nat) (t : Token) (ht : t ∈ table)
    (hsafe : t ≠ rawToken x → x ∉ tokenVariables t) :
    Function.update (parameterValuation table x ν) 0 n (tokenName table x t) =
      t.value (Function.update ν x n) := by
  by_cases h : t = rawToken x
  · subst t
    simp [tokenName, rawToken, Token.value, NormalForm.Summand.term, Term.value]
  · have hn : tokenName table x t ≠ 0 := by
      intro hz
      exact h ((token_name_zero table x t).mp hz)
    rw [Function.update_of_ne hn, parameter_token table x ν t ht]
    exact (token_update t x n ν (hsafe h)).symm

theorem parameter_token_support (p : Formula) (u : Term)
    (hu : Token.parameter u ∈ tokens p) :
    ∀ j ∈ u.variables, j ∈ p.parameters := by
  induction p with
  | truth => simp [tokens] at hu
  | falsity => simp [tokens] at hu
  | atom a =>
    have h : u = a.row.1.1 ∨ u = a.row.1.2 := by
      simpa [tokens, rowTokens, List.mem_map] using hu
    intro j hj
    rcases h with rfl | rfl
    · exact List.mem_append_left _ hj
    · exact List.mem_append_right _ hj
  | negative p ih => exact ih hu
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp hu with hp | hq
    · intro j hj; exact List.mem_append_left _ (ihp hp j hj)
    · intro j hj; exact List.mem_append_right _ (ihq hq j hj)
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp hu with hp | hq
    · intro j hj; exact List.mem_append_left _ (ihp hp j hj)
    · intro j hj; exact List.mem_append_right _ (ihq hq j hj)

theorem occurrence_token_mem (p : Formula) (s : NormalForm.Summand) :
    Token.occurrence s ∈ tokens p ↔ s ∈ (PlainMaximum.occurrences p).map Prod.snd := by
  induction p with
  | truth => simp [tokens, PlainMaximum.occurrences]
  | falsity => simp [tokens, PlainMaximum.occurrences]
  | atom a => simp [tokens, rowTokens, PlainMaximum.occurrences, List.mem_map]
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [tokens, PlainMaximum.occurrences, List.mem_append, List.map_append, ihp, ihq]
  | disjunction p q ihp ihq =>
    simp only [tokens, PlainMaximum.occurrences, List.mem_append, List.map_append, ihp, ihq]

theorem linear_token_safe (x : Nat) (p : Formula) (hp : PlainMaximum.linearIn x p = true)
    (t : Token) (ht : t ∈ tokens p) : t ≠ rawToken x → x ∉ tokenVariables t := by
  have hparams : x ∉ p.parameters := by
    have h := (Bool.and_eq_true_iff.mp hp).1
    simpa using h
  have hall : ∀ a ∈ PlainMaximum.occurrences p, PlainMaximum.linearSummand x a.2 = true :=
    List.all_eq_true.mp (Bool.and_eq_true_iff.mp hp).2
  intro hraw
  cases t with
  | parameter u =>
    intro hx
    exact hparams (parameter_token_support p u ht x hx)
  | occurrence s =>
    obtain ⟨a, ha, hs⟩ := List.mem_map.mp ((occurrence_token_mem p s).mp ht)
    have hlin : PlainMaximum.linearSummand x s = true := by
      rw [← hs]
      exact hall a ha
    cases s with
    | «variable» j =>
      intro hx
      have h : x = j := List.mem_singleton.mp hx
      subst j
      exact hraw rfl
    | phi j shift =>
      have h : j ≠ x := by simpa [PlainMaximum.linearSummand] using hlin
      intro hx
      exact h (List.mem_singleton.mp hx).symm
    | hyperPhi j e h =>
      have hne : j ≠ x := by simpa [PlainMaximum.linearSummand] using hlin
      intro hx
      exact hne (List.mem_singleton.mp hx).symm

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearProof
