module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowTargets
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow.Proof
open CotreeGrammar

variable {Q : Type} [Fintype Q] [DecidableEq Q]

def leafCounts (B : Finset Q) (q : Q) : Counts Q :=
  ⟨fun _ => 0, fun p => if p = (B,q) then 1 else 0⟩

def nodeCounts (r s : Q) (a b : Counts Q) : Counts Q :=
  ⟨fun p => a.binary p + b.binary p + if p = (r,s) then 1 else 0,
    fun p => a.terminal p + b.terminal p⟩

theorem leaf_realizes (δ : Q → Q → Q) (B : Finset Q) (q : Q) (hq : q ∈ B) :
    Realizes δ q [B] (leafCounts B q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C r hr
    simp only [leafCounts]
    split_ifs with he
    · cases he; exact (hr hq).elim
    · rfl
  · intro C
    by_cases hC : C = B
    · subst C; simp [terminalTotal, leafCounts]
    · simp [terminalTotal, leafCounts, Prod.mk.injEq, hC, Ne.symm hC]
  · intro r
    by_cases hr : r = q
    · subst r; simp [consumed, produced, leafCounts]
    · simp [consumed, produced, leafCounts, Prod.mk.injEq, hr, Ne.symm hr]

theorem node_terminal (r s : Q) (a b : Counts Q) (B : Finset Q) :
    terminalTotal (nodeCounts r s a b) B = terminalTotal a B + terminalTotal b B := by
  simp [terminalTotal, nodeCounts, Finset.sum_add_distrib]

theorem indicator_add (P : Prop) [Decidable P] (a b : Nat) :
    (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
  split <;> simp_all

theorem node_consumed (δ : Q → Q → Q) (r s q : Q) (a b : Counts Q) :
    consumed δ (nodeCounts r s a b) q =
      consumed δ a q + consumed δ b q + if δ r s = q then 1 else 0 := by
  simp only [consumed, nodeCounts, indicator_add, Finset.sum_add_distrib]
  have hextra : (∑ p : Q × Q, if δ p.1 p.2 = q then (if p = (r,s) then 1 else 0) else 0) =
      if δ r s = q then 1 else 0 := by
    calc
      _ = ∑ p : Q × Q, if p = (r,s) then (if δ r s = q then 1 else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : p = (r,s) <;> simp [hp]
      _ = _ := by simp
  rw [hextra]
  omega

theorem node_produced (r s q : Q) (a b : Counts Q) :
    produced (nodeCounts r s a b) q = produced a q + produced b q +
      ((if r = q then 1 else 0) + (if s = q then 1 else 0)) := by
  simp only [produced, nodeCounts, Nat.add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, one_mul]
  simp
  <;> omega

theorem node_realizes (δ : Q → Q → Q) {r s : Q} {u v : List (Finset Q)}
    {a b : Counts Q} (ha : Realizes δ r u a) (hb : Realizes δ s v b) :
    Realizes δ (δ r s) (u ++ v) (nodeCounts r s a b) := by
  rcases ha with ⟨has,hat,haf⟩
  rcases hb with ⟨hbs,hbt,hbf⟩
  refine ⟨?_, ?_, ?_⟩
  · intro B q hq
    simp only [nodeCounts, has B q hq, hbs B q hq, Nat.zero_add]
  · intro B
    rw [node_terminal, hat, hbt, List.count_append]
  · intro q
    rw [node_consumed, node_produced, haf, hbf]
    omega

theorem grammarFlowNecessary : Targets.GrammarFlowNecessary := by
  intro Q _ _ δ q w h
  have hb := (CotreeGrammar.StatementChecks.grammarLanguageExact Q δ q w).mp h
  clear h
  induction hb with
  | leaf B q hq => exact ⟨leafCounts B q, leaf_realizes δ B q hq⟩
  | node _ _ ihl ihr =>
    rcases ihl with ⟨a,ha⟩
    rcases ihr with ⟨b,hb⟩
    exact ⟨_,node_realizes δ ha hb⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow.Proof
