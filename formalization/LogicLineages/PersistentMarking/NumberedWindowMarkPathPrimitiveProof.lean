import LogicLineages.PersistentMarking.NumberedWindowMarkPathFiniteProof

namespace LogicLineages.PersistentMarking.NumberedWindowMarkPathPrimitiveProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPreservationTargets
open NumberedWindowClosing NumberedWindowTraceAlgebra NumberedWindowMarkPathTargets
open NumberedWindowMarkPathFiniteProof (typedAtLabel typedChain)

private theorem liftRawLambda {S K C σ τ q r}
    (p : TypedTrace S K (Spine.BoundContext.push C σ) τ q r) :
    onlyRaw p → ∃ path : TypedTrace S K C (.arrow σ τ) (.lam σ q) (.lam σ r),
      onlyRaw path ∧ rawLength path = rawLength p := by
  induction p with
  | done h => intro _; exact ⟨.done (.lam h),True.intro,rfl⟩
  | raw hq hr hs rest ih =>
    intro hp
    obtain ⟨tail,hRaw,hLen⟩ := ih hp
    exact ⟨.raw (.lam hq) (.lam hr) (.lam hs) tail,hRaw,by simp only [rawLength,hLen]⟩
  | equiv he rest ih =>
    intro hp
    exact False.elim hp

private theorem finitePositive {S K C f τ k l bs es}
    (h : l < k) (ht : Typed C (.numbered f τ k bs es) τ) :
    ∃ path : TypedTrace S K C τ (.numbered f τ k bs es) (.numbered f τ l bs es),
      onlyRaw path ∧ 0 < rawLength path := by
  obtain ⟨path,hRaw,hLength⟩ :=
    typedChain S K C f τ bs es k l (Nat.le_of_lt h) (typedAtLabel ht)
  exact ⟨path,hRaw,by rw [hLength]; omega⟩

private theorem fromMark {S K q r} (h : MarkDecrease q r) :
    ∀ C τ, Typed C q τ → ∃ path : TypedTrace S K C τ q r,
      onlyRaw path ∧ 0 < rawLength path := by
  induction h with
  | omega =>
    intro C τ ht
    cases ht with
    | ordinary hb =>
      exact ⟨.raw (.ordinary hb) (.numbered hb .nil) .mark (.done (.numbered hb .nil)),
        True.intro,Nat.zero_lt_succ _⟩
  | finite hl =>
    intro C τ ht
    cases ht with
    | numbered hb he => exact finitePositive hl (.numbered hb he)
  | lam _ ih =>
    intro C τ ht
    cases ht with
    | lam hb =>
      obtain ⟨p,hRaw,hPos⟩ := ih _ _ hb
      obtain ⟨out,hRaw',hLen⟩ := liftRawLambda p hRaw
      exact ⟨out,hRaw',by rw [hLen]; exact hPos⟩

theorem primitive : ArbitraryMarkDecreasePath := by
  intro S K C τ q r hk hw hd
  obtain ⟨path,hRaw,hPos⟩ := fromMark hd C τ hw.1
  exact ⟨path,hRaw,hPos,
    NumberedWindowPreservationChecks.exact_AllTypedTraceIntermediates S K C τ q r hk hw path⟩

end LogicLineages.PersistentMarking.NumberedWindowMarkPathPrimitiveProof
