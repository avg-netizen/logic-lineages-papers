module
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceDisplayedHeads

theorem validity : Targets.DisplayedSourceHeadValidity := by
  intro E
  induction E with
  | constant n => intro _ p h; cases h
  | input => intro _ p h; cases h
  | add E F ihE ihF =>
    intro hv p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ihE hv.1 p hp
    · exact ihF hv.2 p hp
  | head rho E ih =>
    intro hv p hp
    by_cases hinput : positiveExprHasInput E=true
    · simp only [comparisonDisplayedSourceHeads,if_pos hinput,List.mem_singleton] at hp
      subst p
      exact ⟨hv.1,hv.2.1,hv.2.2,hinput⟩
    · simp only [comparisonDisplayedSourceHeads,if_neg hinput] at hp
      cases hp

theorem budget : Targets.DisplayedSourceHeadOccurrenceBudget := by
  intro E
  induction E with
  | constant n => exact Nat.le_refl 0
  | input => exact Nat.le_refl 0
  | add E F ihE ihF =>
    simp only [comparisonDisplayedSourceHeads,comparisonPositiveSourceHeadCount,List.map_append,List.sum_append]
    exact Nat.add_le_add ihE ihF
  | head rho E ih =>
    by_cases hinput : positiveExprHasInput E=true
    · simp [comparisonDisplayedSourceHeads,comparisonPositiveSourceHeadCount,hinput]
    · simp [comparisonDisplayedSourceHeads,comparisonPositiveSourceHeadCount,hinput]

private theorem member_weight {A : Type} (f : A → Nat) (L : List A) (p : A) (hp : p∈L) :
    f p≤(L.map f).sum := by
  induction L with
  | nil => cases hp
  | cons q L ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hp with h | h
    · subst p
      exact Nat.le_add_right _ _
    · have hh := ih h
      omega

private theorem pair_weight {A : Type} (f : A → Nat) (L : List A) (p q : A)
    (hp : p∈L) (hq : q∈L) (hne : p≠q) : f p+f q≤(L.map f).sum := by
  induction L with
  | nil => cases hp
  | cons r L ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp hp with hP | hP
    · rcases List.mem_cons.mp hq with hQ | hQ
      · exact (hne (hP.trans hQ.symm)).elim
      · subst p
        have hh := member_weight f L q hQ
        omega
    · rcases List.mem_cons.mp hq with hQ | hQ
      · subst q
        have hh := member_weight f L p hP
        omega
      · have hh := ih hP hQ
        omega

theorem argument_drop : Targets.DisplayedSourceArgumentDrop := by
  constructor
  · intro E p hp
    have hm := member_weight (fun p : NONote × FixedLimitPositiveExpr => comparisonPositiveSourceHeadCount p.2+1)
      (comparisonDisplayedSourceHeads E) p hp
    have hb := budget E
    change comparisonPositiveSourceHeadCount p.2+1≤_ at hm
    omega
  · intro E F p q hp hq hne
    have hm := pair_weight (fun p : NONote × FixedLimitPositiveExpr => comparisonPositiveSourceHeadCount p.2+1)
      (comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F) p q hp hq hne
    have hbE := budget E
    have hbF := budget F
    simp only [List.map_append,List.sum_append] at hm
    change (comparisonPositiveSourceHeadCount p.2+1)+(comparisonPositiveSourceHeadCount q.2+1)≤_ at hm
    omega

end LogicLineages.OrdinalComparison.SourceDisplayedHeads
