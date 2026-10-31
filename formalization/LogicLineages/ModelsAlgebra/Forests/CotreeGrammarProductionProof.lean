module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProductionTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotationStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction.Proof
open CotreeGrammarOpen CotreeGrammarRotation CotreeGrammarFlow CotreeGrammarFlow.Proof
open CotreeGrammarOpen.Proof CotreeGrammarRotation.Proof

theorem binaryFactorization : Targets.BinaryFactorization := by
  intro Q _ δ q t r s
  constructor
  · induction t with
    | hole q => simp [counts, zeroCounts]
    | terminal B q hq => simp [counts, leafCounts]
    | @branch a b l u ihl ihu =>
      intro h
      by_cases he : (r,s) = (a,b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨.hole _, l, u, rfl⟩
      · have hp : 0 < (counts l).binary (r,s) ∨ 0 < (counts u).binary (r,s) := by
          simp only [counts, nodeCounts, if_neg he] at h
          omega
        rcases hp with hp | hp
        · obtain ⟨C, l', u', hC⟩ := ihl hp
          exact ⟨.left C u, l', u', by simp only [plug, hC]⟩
        · obtain ⟨C, l', u', hC⟩ := ihu hp
          exact ⟨.right l C, l', u', by simp only [plug, hC]⟩
  · rintro ⟨C, l, u, rfl⟩
    rw [plugCounts]
    simp only [addCounts, counts, nodeCounts, ite_true]
    omega

theorem containsPlug {Q : Type} {δ : Q → Q → Q} {r q} (C : Context δ r q) (u : Tree δ q) :
    Contains u (plug C u) := by
  induction C with
  | hole => exact Contains.root
  | left C t ih => exact Contains.left (ih u)
  | right t C ih => exact Contains.right (ih u)

theorem containsFactorization : Targets.ContainsFactorization := by
  intro Q δ r q t u
  constructor
  · intro h
    induction h with
    | root => exact ⟨.hole q, rfl⟩
    | @left r s l t h ih =>
      obtain ⟨C, he⟩ := ih
      exact ⟨.left C t, by simp only [plug, he]⟩
    | @right r s l t h ih =>
      obtain ⟨C, he⟩ := ih
      exact ⟨.right l C, by simp only [plug, he]⟩
  · rintro ⟨C, rfl⟩
    exact containsPlug C u

theorem containsCases {Q : Type} {δ : Q → Q → Q} {r q} {u : Tree δ q} {t : Tree δ r}
    (h : Contains u t) : (∃ h : q = r, h ▸ u = t) ∨ (match t with
      | .branch l v => Contains u l ∨ Contains u v
      | _ => False) := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl⟩
  | left h => exact Or.inr (Or.inl h)
  | right h => exact Or.inr (Or.inr h)

theorem exactContextDichotomy : Targets.ExactContextDichotomy := by
  intro Q δ r x C
  induction C with
  | hole x =>
    intro y u h
    rcases containsCases h with ⟨he, hu⟩ | h
    · subst y
      exact Or.inl ⟨.hole x, .hole x, rfl, hu⟩
    · exact h.elim
  | @left r s x C t ih =>
    intro y u h
    rcases containsCases h with ⟨he, hu⟩ | h
    · subst y
      exact Or.inl ⟨.hole _, .left C t, rfl, hu⟩
    · rcases h with h | h
      · rcases ih y u h with ⟨P, S, he, hu⟩ | ⟨D, he⟩
        · exact Or.inl ⟨.left P t, S, by rw [he]; rfl, hu⟩
        · exact Or.inr ⟨.left D t, fun v => congrArg (fun z => Tree.branch z t) (he v)⟩
      · obtain ⟨D, he⟩ := (containsFactorization Q δ s y t u).mp h
        exact Or.inr ⟨.forkSwap C D, fun v => by simp only [plug, fill, he]⟩
  | @right r s x t C ih =>
    intro y u h
    rcases containsCases h with ⟨he, hu⟩ | h
    · subst y
      exact Or.inl ⟨.hole _, .right t C, rfl, hu⟩
    · rcases h with h | h
      · obtain ⟨D, he⟩ := (containsFactorization Q δ r y t u).mp h
        exact Or.inr ⟨.fork D C, fun v => by simp only [plug, fill, he]⟩
      · rcases ih y u h with ⟨P, S, he, hu⟩ | ⟨D, he⟩
        · exact Or.inl ⟨.right t P, S, by rw [he]; rfl, hu⟩
        · exact Or.inr ⟨.right t D, fun v => congrArg (fun z => Tree.branch t z) (he v)⟩

private theorem branchChildFactor {Q : Type} {δ : Q → Q → Q} {r s x}
    (l : Tree δ r) (u : Tree δ s) (h : r = x ∨ s = x) :
    ∃ (C : Context δ (δ r s) x) (v : Tree δ x), plug C v = Tree.branch l u := by
  rcases h with rfl | rfl
  · exact ⟨.left (.hole _) u, l, rfl⟩
  · exact ⟨.right l (.hole _), u, rfl⟩

theorem cycleRotateProduction : Targets.CycleRotateProduction := by
  intro Q _ δ x t r s hh hp hc
  obtain ⟨C, l, u, hC⟩ := (binaryFactorization Q δ x t r s).mp hp
  obtain ⟨D, hD⟩ := (holeFactorization Q δ x t x).mp (by rw [hh]; exact List.mem_singleton_self x)
  have hsub : Contains (Tree.branch l u) (plug D (.hole x)) := by
    rw [hD, ← hC]
    exact containsPlug C _
  rcases exactContextDichotomy Q δ x x D (δ r s) (Tree.branch l u) hsub with
      ⟨P, S, hDS, _⟩ | ⟨E, hE⟩
  · have he : plug (compose P S) (.hole x) = t := by rw [← hDS]; exact hD
    have hr := onPathRotation Q δ x (δ r s) P S
    refine ⟨plug (compose S P) (.hole (δ r s)), hr.2 ((congrArg holes he).trans hh), ?_⟩
    exact hr.1.symm.trans (congrArg counts he)
  · obtain ⟨K, v, hv⟩ := branchChildFactor l u hc
    have he : fill E (plug K v) (.hole x) = t := by
      rw [hv, ← hE]
      exact hD
    have hr := offPathRotation Q δ x (δ r s) E K v
    refine ⟨plug K (fill E (.hole (δ r s)) v), hr.2 ((congrArg holes he).trans hh), ?_⟩
    exact hr.1.symm.trans (congrArg counts he)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction.Proof
