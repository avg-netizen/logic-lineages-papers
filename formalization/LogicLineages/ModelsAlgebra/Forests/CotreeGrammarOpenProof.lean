module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpenTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen.Proof
open CotreeGrammarFlow CotreeGrammarFlow.Proof

theorem countExt {Q : Type} (a b : Counts Q)
    (hb : ∀ p, a.binary p = b.binary p) (ht : ∀ p, a.terminal p = b.terminal p) : a = b :=
  congrArg₂ Counts.mk (funext hb) (funext ht)

theorem treeBalance : Targets.TreeBalance := by
  intro Q _ _ δ q t
  induction t with
  | hole q =>
    intro r
    by_cases h : q = r <;> simp [counts, zeroCounts, consumed, produced, holes, h, Ne.symm, List.count_cons, beq_iff_eq]
  | terminal B q hq =>
    intro r
    simpa only [counts, holes, List.count_nil, Nat.add_zero] using (leaf_realizes δ B q hq).2.2 r
  | @branch r s l t hl ht =>
    intro q
    simp only [counts, holes, List.count_append, node_consumed, node_produced]
    have h₁ := hl q
    have h₂ := ht q
    omega

theorem treeTerminals : Targets.TreeTerminals := by
  intro Q _ _ δ q t
  induction t with
  | hole q => simp [counts, zeroCounts, terminalTotal, word]
  | terminal B q hq => exact ⟨(leaf_realizes δ B q hq).2.1, (leaf_realizes δ B q hq).1⟩
  | @branch r s l t hl ht =>
    constructor
    · intro B
      simp only [counts, word, List.count_append, node_terminal, hl.1 B, ht.1 B]
    · intro B q hq
      simp only [counts, nodeCounts, hl.2 B q hq, ht.2 B q hq, Nat.zero_add]

theorem closedBuilds : Targets.ClosedBuilds := by
  intro Q δ q t
  induction t with
  | hole q => simp [holes]
  | terminal B q hq => intro _; exact CotreeGrammar.Builds.leaf B q hq
  | branch l r hl hr =>
    intro h
    have hp := List.append_eq_nil_iff.mp h
    exact CotreeGrammar.Builds.node (hl hp.1) (hr hp.2)

theorem buildsClosedTree : Targets.BuildsClosedTree := by
  intro Q δ q w h
  induction h with
  | leaf B q hq => exact ⟨.terminal B q hq, rfl, rfl⟩
  | node _ _ hl hr =>
    obtain ⟨l, hhl, hwl⟩ := hl
    obtain ⟨r, hhr, hwr⟩ := hr
    exact ⟨.branch l r, by simp [holes, hhl, hhr], by simp [word, hwl, hwr]⟩

theorem plugCounts : Targets.PlugCounts := by
  intro Q _ δ r q C
  induction C with
  | hole q =>
    intro t
    apply countExt <;> intro p <;> simp [plug, contextCounts, counts, zeroCounts, addCounts]
  | @left r s q C t ih =>
    intro u
    change nodeCounts r s (counts (plug C u)) (counts t) =
      addCounts (nodeCounts r s (contextCounts C) (counts t)) (counts u)
    rw [ih]
    apply countExt <;> intro p <;> simp only [nodeCounts, addCounts] <;> omega
  | @right r s q t C ih =>
    intro u
    change nodeCounts r s (counts t) (counts (plug C u)) =
      addCounts (nodeCounts r s (counts t) (contextCounts C)) (counts u)
    rw [ih]
    apply countExt <;> intro p <;> simp only [nodeCounts, addCounts] <;> omega

theorem holeMemPlug {Q : Type} {δ : Q → Q → Q} {r q} (C : Context δ r q) :
    q ∈ holes (plug C (.hole q)) := by
  induction C with
  | hole => simp [plug, holes]
  | left C t ih => exact List.mem_append_left _ ih
  | right t C ih => exact List.mem_append_right _ ih

theorem holeFactorization : Targets.HoleFactorization := by
  intro Q δ r t q
  constructor
  · induction t with
    | hole r =>
      intro h
      have hq : q = r := List.mem_singleton.mp h
      subst q
      exact ⟨.hole r, rfl⟩
    | terminal B r h => simp [holes]
    | @branch r s l t hl ht =>
      intro h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨C, hC⟩ := hl h
        exact ⟨.left C t, by simp only [plug, hC]⟩
      · obtain ⟨C, hC⟩ := ht h
        exact ⟨.right l C, by simp only [plug, hC]⟩
  · rintro ⟨C, rfl⟩
    exact holeMemPlug C

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen.Proof
