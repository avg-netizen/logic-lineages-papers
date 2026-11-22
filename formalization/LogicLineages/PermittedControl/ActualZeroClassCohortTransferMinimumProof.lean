module
public import LogicLineages.PermittedControl.ActualZeroClassCohortTransferTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassCohortTransfer

private theorem noneIffEmpty (ps : List SurvivingPrefix) : leastPrefix ps = none ↔ ps = [] := by
  cases ps with
  | nil => simp [leastPrefix]
  | cons p ps =>
      constructor
      · intro empty
        cases tail : leastPrefix ps with
        | none => simp [leastPrefix,tail] at empty
        | some q =>
            by_cases first : p.rank ≤ q.rank <;> simp [leastPrefix,tail,first] at empty
      · intro empty
        cases empty

theorem exactLeastPrefix : ExactLeastPrefix := by
  refine ⟨noneIffEmpty,?_⟩
  intro ps
  induction ps with
  | nil =>
      intro anchor found
      cases found
  | cons p ps next =>
      intro anchor found
      cases tail : leastPrefix ps with
      | none =>
          have empty := (noneIffEmpty ps).mp tail
          subst ps
          simp only [leastPrefix,Option.some.injEq] at found
          subst anchor
          refine ⟨List.mem_cons_self,?_⟩
          intro q member
          have equal : q = p := List.mem_singleton.mp member
          subst q
          exact le_rfl
      | some q =>
          obtain ⟨qMember,qLeast⟩ := next q tail
          by_cases first : p.rank ≤ q.rank
          · simp only [leastPrefix,tail,if_pos first,Option.some.injEq] at found
            subst anchor
            refine ⟨List.mem_cons_self,?_⟩
            intro other member
            rcases List.mem_cons.mp member with equal | remainder
            · subst other
              exact le_rfl
            · exact first.trans (qLeast other remainder)
          · simp only [leastPrefix,tail,if_neg first,Option.some.injEq] at found
            subst anchor
            refine ⟨List.mem_cons_of_mem _ qMember,?_⟩
            intro other member
            rcases List.mem_cons.mp member with equal | remainder
            · subst other
              exact Nat.le_of_lt (Nat.lt_of_not_ge first)
            · exact qLeast other remainder

end LogicLineages.PermittedControl.ActualZeroClassCohortTransfer
