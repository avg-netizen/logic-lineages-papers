module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForestTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForest.Proof
open CotreeGrammarFlow CotreeGrammarOpen CotreeGrammarForest

@[simp] theorem sum_chunks {α β : Type} (xs : List α) (chunk : α → List β) (f : β → Nat) :
    ((xs.flatMap chunk).map f).sum = (xs.map (fun a => ((chunk a).map f).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

@[simp] theorem sum_univ_list {α : Type} [Fintype α] (f : α → Nat) :
    (Finset.univ.toList.map f).sum = ∑ a, f a := by
  classical
  rw [← List.sum_toFinset f Finset.univ.nodup_toList, Finset.toList_toFinset]

variable {Q : Type} [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (c : Counts Q)

@[simp] theorem binary_chunk_binary (p z : Q × Q) :
    ((List.replicate (c.binary p)
      (⟨δ p.1 p.2, Tree.branch (.hole p.1) (.hole p.2)⟩ : Packed δ)).map
      (fun t => (counts t.2).binary z)).sum = if z = p then c.binary p else 0 := by
  rcases p with ⟨r,s⟩
  simp [counts, zeroCounts, CotreeGrammarFlow.Proof.nodeCounts, nsmul_eq_mul, mul_ite]

@[simp] theorem binary_chunk_terminal (p : Q × Q) (z : Finset Q × Q) :
    ((List.replicate (c.binary p)
      (⟨δ p.1 p.2, Tree.branch (.hole p.1) (.hole p.2)⟩ : Packed δ)).map
      (fun t => (counts t.2).terminal z)).sum = 0 := by
  simp [counts, zeroCounts, CotreeGrammarFlow.Proof.nodeCounts]

@[simp] theorem terminal_chunk_binary (p : Finset Q × Q) (z : Q × Q) :
    ((if h : p.2 ∈ p.1 then List.replicate (c.terminal p)
      (⟨p.2, Tree.terminal p.1 p.2 h⟩ : Packed δ) else []).map
      (fun t => (counts t.2).binary z)).sum = 0 := by
  split <;> simp [counts, CotreeGrammarFlow.Proof.leafCounts]

@[simp] theorem terminal_chunk_terminal
    (hc : ∀ B q, q ∉ B → c.terminal (B,q) = 0) (p z : Finset Q × Q) :
    ((if h : p.2 ∈ p.1 then List.replicate (c.terminal p)
      (⟨p.2, Tree.terminal p.1 p.2 h⟩ : Packed δ) else []).map
      (fun t => (counts t.2).terminal z)).sum = if z = p then c.terminal p else 0 := by
  rcases p with ⟨B,q⟩
  split
  · simp [counts, CotreeGrammarFlow.Proof.leafCounts, nsmul_eq_mul, mul_ite]
  · rename_i h
    simp [hc B q h]

theorem initialForestExact : Targets.InitialForestExact := by
  intro Q _ _ δ c hc
  apply CotreeGrammarOpen.Proof.countExt
  · intro z
    simp only [initialForest, forestCounts, List.map_append, List.sum_append,
      sum_chunks, sum_univ_list, binary_chunk_binary, terminal_chunk_binary]
    simp
  · intro z
    simp only [initialForest, forestCounts, List.map_append, List.sum_append,
      sum_chunks, sum_univ_list, binary_chunk_terminal, terminal_chunk_terminal δ c hc]
    simp

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForest.Proof
