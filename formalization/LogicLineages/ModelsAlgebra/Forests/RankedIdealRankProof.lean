module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRankTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRank.Proof
open ProfileAutomatonEncoding RankedIdealFinite RankedIdealComponents RankedIdealCompletion
 theorem reachReflexive : Targets.ReachReflexive := by
  intro M _ q
  exact (RankedIdealFinite.StatementChecks.closureExact M {q} q).mpr (.seed (by simp))
 theorem reachTransitive : Targets.ReachTransitive := by
  intro M _ p q r hp hq
  have hc := (RankedIdealFinite.StatementChecks.closureExact M {q} r).mp hq
  have hp' := (RankedIdealFinite.StatementChecks.closureExact M {p} q).mp hp
  clear hp hq
  apply (RankedIdealFinite.StatementChecks.closureExact M {p} r).mpr
  induction hc with
  | seed h =>
      rw [Finset.mem_singleton.mp h]
      exact hp'
  | edge _ he ih => exact .edge ih he
 theorem componentRank : Targets.ComponentRank := by
  intro M _ p q h
  have he : predecessors M p = predecessors M q := by
    ext x
    simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hx => reachTransitive M x p q hx h.1,
      fun hx => reachTransitive M x q p hx h.2⟩
  exact congrArg Finset.card he
 theorem lowerRank : Targets.LowerRank := by
  intro M _ p q h
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact reachTransitive M x p q hx h.1
  · intro he
    have hq : q ∈ predecessors M q := by simp [predecessors, reachReflexive M q]
    rw [← he] at hq
    exact h.2 (Finset.mem_filter.mp hq).2
 theorem predecessorCases : Targets.PredecessorCases := by
  intro M _ p q h
  by_cases hr : p ∈ close M {q}
  · exact Or.inl ⟨h, hr⟩
  · exact Or.inr ⟨h, hr⟩
 theorem linearChildren : Targets.LinearChildren := by
  intro M _ q o x y hn hx hy hc
  have ex : Epsilon M x (M.node o x y) := ⟨hx, o, y, hy, Or.inl rfl⟩
  have ey : Epsilon M y (M.node o x y) := ⟨hy, o, x, hx, Or.inr rfl⟩
  have edge (a b) (h : Epsilon M a b) : b ∈ close M {a} :=
    (RankedIdealFinite.StatementChecks.closureExact M {a} b).mpr (.edge (.seed (by simp)) h)
  have px := reachTransitive M x (M.node o x y) q (edge _ _ ex) hc.2
  have py := reachTransitive M y (M.node o x y) q (edge _ _ ey) hc.2
  rcases predecessorCases M x q px with hcx | hlx
  · have hqx : SameComponent M q x := ⟨hcx.2, hcx.1⟩
    rcases predecessorCases M y q py with hcy | hly
    · exact False.elim (hn ⟨o, x, y, hx, hy, hqx, ⟨hcy.2, hcy.1⟩, hc⟩)
    · exact Or.inr (Or.inl ⟨hqx, hly⟩)
  · rcases predecessorCases M y q py with hcy | hly
    · exact Or.inr (Or.inr ⟨hlx, ⟨hcy.2, hcy.1⟩⟩)
    · exact Or.inl ⟨hlx, hly⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRank.Proof
