import LogicLineages.PersistentMarking.NumberedWindowTypingBitsTargets

namespace LogicLineages.PersistentMarking.NumberedWindowLiteralEqualityProof
open NumberedWindowSyntax NumberedWindowLiteralEquality NumberedWindowTypingBitsTargets

theorem term : LiteralTermEquality := by
  intro Q
  induction Q using NTerm.rec (motive_2 := fun qs => ∀ rs, argsEq qs rs = true ↔ qs = rs) with
  | free σ x => intro R; cases R <;> simp [termEq]
  | bound σ i => intro R; cases R <;> simp [termEq]
  | lam σ q ih => intro R; cases R <;> simp [termEq,ih]
  | bottom σ => intro R; cases R <;> simp [termEq]
  | ordinary f qs ih => intro R; cases R <;> simp [termEq,ih]
  | numbered f τ k bs es ihB ihE =>
    intro R; cases R <;> simp [termEq,ihB,ihE,and_assoc]
  | auxApp σ τ q a ihQ ihA =>
    intro R; cases R <;> simp [termEq,ihQ,ihA,and_assoc]
  | nil => intro rs; cases rs <;> simp [argsEq]
  | cons q qs ihQ ihA =>
    intro rs; cases rs <;> simp [argsEq,ihQ,ihA]

theorem args : LiteralArgsEquality := by
  intro qs rs
  have h := term (.ordinary .zero qs) (.ordinary .zero rs)
  simpa [termEq] using h

end LogicLineages.PersistentMarking.NumberedWindowLiteralEqualityProof
