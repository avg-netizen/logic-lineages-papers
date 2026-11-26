import LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets
import LogicLineages.PersistentMarking.NumberedWindowRealizationShapeProof

namespace LogicLineages.PersistentMarking.NumberedWindowReservedMarkShapeProof
open NumberedWindowSyntax NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowRealizationShapeProof (weakensArgs)

private theorem lower {S K n f τ k bs es Bs Es}
    (hk : n+1 ≤ k) (hb : RealizesArgs (n+1) bs Bs) (he : RealizesArgs (n+1) es Es) :
    ∃ R, MarkDecrease (.numbered f τ k Bs Es) R ∧ RawStep S K (.numbered f τ k Bs Es) R ∧
      Realizes n (.marked f τ bs es) R := by
  cases k with
  | zero => omega
  | succ k =>
    refine ⟨.numbered f τ k Bs Es,.finite (Nat.lt_succ_self k),.lower,?_⟩
    exact .marked (Nat.le_of_succ_le_succ hk)
      (weakensArgs (Nat.le_succ n) hb) (weakensArgs (Nat.le_succ n) he)

theorem step (S : Spine.Signature) (K : List Ty) (n : Nat) (q r : Spine.Expr) (Q : NTerm)
    (hm : Spine.mark q = some r) (hQ : Realizes (n+1) q Q) :
    ∃ R, MarkDecrease Q R ∧ RawStep S K Q R ∧ Realizes n r R := by
  cases q with
  | free σ x => simp [Spine.mark] at hm
  | bound σ i => simp [Spine.mark] at hm
  | lam σ body =>
    cases he : Spine.mark body with
    | none => simp [Spine.mark,he] at hm
    | some out =>
      simp only [Spine.mark,he,Option.map_some,Option.some.injEq] at hm
      subst r
      cases hQ with
      | lam hb =>
        obtain ⟨R,hd,hs,hR⟩ := step S K n body out _ he hb
        exact ⟨.lam σ R,.lam hd,.lam hs,.lam hR⟩
  | head f bs =>
    simp only [Spine.mark,Option.some.injEq] at hm
    subst r
    cases hQ with
    | ordinary hb =>
      exact ⟨.numbered f f.result n _ .nil,.omega,.mark,
        .marked (Nat.le_refl n) (weakensArgs (Nat.le_succ n) hb) .nil⟩
  | marked f τ bs es =>
    simp only [Spine.mark,Option.some.injEq] at hm
    subst r
    cases hQ with
    | marked hk hb he => exact lower hk hb he
termination_by sizeOf q

end LogicLineages.PersistentMarking.NumberedWindowReservedMarkShapeProof
