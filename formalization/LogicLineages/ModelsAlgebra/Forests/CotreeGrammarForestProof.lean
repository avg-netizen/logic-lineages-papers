module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForestTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest.Proof
open CotreeGrammarFlow CotreeGrammarOpen CotreeGrammarOpen.Proof

variable {Q : Type} [DecidableEq Q] {δ : Q → Q → Q}

theorem counts_nil : forestCounts ([] : List (Packed δ)) = zeroCounts Q := rfl

theorem counts_cons (t : Packed δ) (F : List (Packed δ)) :
    forestCounts (t :: F) = addCounts (counts t.2) (forestCounts F) := by
  apply countExt <;> intro p <;> simp [forestCounts, addCounts]

theorem counts_perm {F G : List (Packed δ)} (h : F.Perm G) : forestCounts F = forestCounts G := by
  apply countExt
  · intro p; exact (h.map (fun t => (counts t.2).binary p)).sum_eq
  · intro p; exact (h.map (fun t => (counts t.2).terminal p)).sum_eq

theorem consumed_add [Fintype Q] (δ : Q → Q → Q) (a b : Counts Q) q :
    consumed δ (addCounts a b) q = consumed δ a q + consumed δ b q := by
  simp only [consumed, addCounts, CotreeGrammarFlow.Proof.indicator_add, Finset.sum_add_distrib]
  omega

theorem produced_add [Fintype Q] (a b : Counts Q) q :
    produced (addCounts a b) q = produced a q + produced b q := by
  simp only [produced, addCounts, Nat.add_mul, Finset.sum_add_distrib]

theorem terminal_add [Fintype Q] (a b : Counts Q) B :
    terminalTotal (addCounts a b) B = terminalTotal a B + terminalTotal b B := by
  simp only [terminalTotal, addCounts, Finset.sum_add_distrib]

theorem forestBalance : Targets.ForestBalance := by
  intro Q _ _ δ F
  induction F with
  | nil => intro q; simp [counts_nil, zeroCounts, consumed, produced, forestHoles, roots]
  | cons t F ih =>
    intro q
    rw [counts_cons, consumed_add, produced_add]
    simp only [forestHoles, roots, List.flatMap_cons, List.map_cons, List.count_append,
      List.count_cons, beq_iff_eq]
    have ht := CotreeGrammarOpen.StatementChecks.treeBalance Q δ t.1 t.2 q
    have hh := ih q
    change consumed δ (forestCounts F) q + (forestHoles F).count q =
      (roots F).count q + produced (forestCounts F) q at hh
    unfold forestHoles roots at hh
    by_cases he : t.1 = q
    · simp [he] at ht ⊢; omega
    · simp [he, Ne.symm he] at ht ⊢; omega

theorem forestTerminals : Targets.ForestTerminals := by
  intro Q _ _ δ F
  induction F with
  | nil => intro B; simp [counts_nil,zeroCounts,terminalTotal,forestWord]
  | cons t F ih =>
    intro B
    rw [counts_cons, terminal_add]
    have ht := (CotreeGrammarOpen.StatementChecks.treeTerminals Q δ t.1 t.2).1 B
    simpa only [forestWord, List.flatMap_cons, List.count_append] using congrArg₂ (· + ·) ht (ih B)

theorem merge_counts {r q : Q} (C : Context δ r q) (t : Tree δ q) (rest : List (Packed δ)) :
    forestCounts (⟨r,plug C t⟩ :: rest) =
      forestCounts (⟨r,plug C (.hole q)⟩ :: ⟨q,t⟩ :: rest) := by
  simp only [counts_cons]
  rw [CotreeGrammarOpen.StatementChecks.plugCounts Q δ r q C t]
  change addCounts (addCounts (contextCounts C) (counts t)) (forestCounts rest) =
    addCounts (contextCounts C) (addCounts (counts t) (forestCounts rest))
  apply countExt <;> intro p <;> simp only [addCounts] <;> omega

theorem remove_hole_counts (q : Q) (rest : List (Packed δ)) :
    forestCounts rest = forestCounts (⟨q,Tree.hole q⟩ :: rest) := by
  rw [counts_cons]
  apply countExt <;> intro p <;> simp [counts,zeroCounts,addCounts]

theorem normalForestExists : Targets.NormalForestExists := by
  intro Q _ δ F
  classical
  have hex : ∃ n, ∃ G : List (Packed δ), forestCounts G = forestCounts F ∧ G.length = n :=
    ⟨F.length,F,rfl,rfl⟩
  obtain ⟨G,hG,hlen⟩ := Nat.find_spec hex
  have hmin : ∀ H : List (Packed δ), forestCounts H = forestCounts F → G.length ≤ H.length := by
    intro H hH
    rw [hlen]
    exact Nat.find_min' hex ⟨H,hH,rfl⟩
  refine ⟨G,hG,?_,?_⟩
  · intro a ta b tb rest hp hm
    obtain ⟨C,rfl⟩ := (CotreeGrammarOpen.StatementChecks.holeFactorization Q δ a ta b).mp hm
    have hc : forestCounts (⟨a,plug C tb⟩ :: rest) = forestCounts F :=
      (merge_counts C tb rest).trans ((counts_perm hp).symm.trans hG)
    have hle := hmin _ hc
    have hl := hp.length_eq
    simp only [List.length_cons] at hle hl
    omega
  · intro q hq
    have hp := List.perm_cons_erase hq
    have hc : forestCounts (G.erase ⟨q,Tree.hole q⟩) = forestCounts F :=
      (remove_hole_counts q _).trans ((counts_perm hp).symm.trans hG)
    have hle := hmin _ hc
    have hl := hp.length_eq
    simp only [List.length_cons] at hl
    omega

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest.Proof
