module

public import LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleTargets
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Fintype.Card
public import Lean.Elab.Tactic.Omega

/-! The actual induced graph embedding exists, but even the weaker downward
edge-disjoint-path cotree map does not. This is a bounded transfer-clause
counterexample only, not a disproof of the final decision theorem. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof

open CotreeCounterexample

private instance {n} (T : CotreeData n) (x y z) : Decidable (IsLCA T x y z) := by
  unfold IsLCA
  infer_instance

private instance {n} (T : CotreeData n) : DecidableRel (joinLCA T) := by
  intro x y
  unfold joinLCA
  infer_instance

theorem concreteCotreesValid : Targets.ConcreteCotreesValid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ValidCotree
    decide +kernel
  · unfold ValidCotree
    decide +kernel
  · intro x y
    fin_cases x <;> fin_cases y <;> unfold ExistsUnique <;> decide +kernel
  · intro x y
    fin_cases x <;> fin_cases y <;> unfold ExistsUnique <;> decide +kernel

theorem concreteCotreeLeavesExact : Targets.ConcreteCotreeLeavesExact := by
  unfold Targets.ConcreteCotreeLeavesExact Function.Injective
  decide +kernel

private theorem join_symm {n} (T : CotreeData n) (x y) :
    joinLCA T x y ↔ joinLCA T y x := by
  constructor <;> rintro ⟨z, ⟨hx, hy, hz⟩, hl⟩
  · exact ⟨z, ⟨hy, hx, fun w hw₁ hw₂ => hz w hw₂ hw₁⟩, hl⟩
  · exact ⟨z, ⟨hy, hx, fun w hw₁ hw₂ => hz w hw₂ hw₁⟩, hl⟩

private theorem evaluated_adj {n m} (T : CotreeData n) (f : Fin m → Fin n) (i j) :
    (evaluatedGraph T f).Adj i j ↔ i ≠ j ∧ joinLCA T (f i) (f j) := by
  simp only [evaluatedGraph, SimpleGraph.fromRel_adj, ← join_symm T (f i) (f j), or_self]

theorem concreteCotreeGraphsExact : Targets.ConcreteCotreeGraphsExact := by
  refine ⟨?_, ?_, evaluated_adj _ _, evaluated_adj _ _⟩
  · ext i j
    simp only [evaluated_adj, SimpleGraph.bot_adj, iff_false]
    fin_cases i <;> fin_cases j <;> decide +kernel
  · ext i j
    simp only [evaluated_adj, isolatedPathGraph, SimpleGraph.fromRel_adj]
    fin_cases i <;> fin_cases j <;> decide +kernel

private theorem first_step {n} (T : CotreeData n) (p : List (Fin n)) (a b : Fin n)
    (hne : a ≠ b) (hs : p.head? = some a) (he : p.getLast? = some b)
    (hc : p.IsChain (child T)) :
    ∃ c, child T a c ∧ (a, c) ∈ pathEdges p := by
  cases p with
  | nil => simp at hs
  | cons x xs =>
      have hx : x = a := Option.some.inj hs
      subst x
      cases xs with
      | nil => exact (hne (Option.some.inj he)).elim
      | cons c rest =>
          refine ⟨c, (List.isChain_cons_cons.mp hc).1, ?_⟩
          simp [pathEdges]

private theorem host_binary (x : Fin 7) :
    (Finset.univ.filter (child hostCotree x)).card ≤ 2 := by
  fin_cases x <;> decide +kernel

theorem concreteCotreePathObstruction : Targets.ConcreteCotreePathObstruction := by
  classical
  rintro ⟨E⟩
  let edge (i : Fin 3) : Edge sourceCotree :=
    ⟨(0, i.succ), by simp [child, sourceCotree]⟩
  have edge_inj : Function.Injective edge := by
    intro i j h
    exact Fin.succ_injective 3 (congrArg (fun e : Edge sourceCotree => e.val.2) h)
  have first (i : Fin 3) : ∃ c, child hostCotree (E.nodeMap 0) c ∧
      (E.nodeMap 0, c) ∈ pathEdges (E.path (edge i)) := by
    apply first_step hostCotree (E.path (edge i)) (E.nodeMap 0) (E.nodeMap i.succ)
    · intro h
      exact Fin.succ_ne_zero i (E.nodeMap.injective h).symm
    · exact E.path_start (edge i)
    · exact E.path_end (edge i)
    · exact E.path_downward (edge i)
  choose next hchild hmem using first
  let f : Fin 3 → {v : Fin 7 // child hostCotree (E.nodeMap 0) v} :=
    fun i => ⟨next i, hchild i⟩
  have hf : Function.Injective f := by
    intro i j h
    by_contra hij
    have hn : next i = next j := congrArg Subtype.val h
    have hd := E.edge_disjoint (edge i) (edge j) (fun he => hij (edge_inj he))
    exact (Finset.disjoint_left.mp hd) (hmem i) (by simpa only [hn] using hmem j)
  have hbound : Fintype.card {v : Fin 7 // child hostCotree (E.nodeMap 0) v} ≤ 2 := by
    rw [Fintype.card_subtype]
    exact host_binary _
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

theorem literalCotreeTransferCounterexample : Targets.LiteralCotreeTransferCounterexample := by
  refine ⟨concreteCotreesValid.1, concreteCotreesValid.2.1, ?_, concreteCotreePathObstruction⟩
  rw [concreteCotreeGraphsExact.1, concreteCotreeGraphsExact.2.1]
  let f : Fin 3 → Fin 4 := ![0, 2, 3]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨⟨f, hf⟩, ?_⟩⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [f, isolatedPathGraph, SimpleGraph.fromRel_adj]

end LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleProof
