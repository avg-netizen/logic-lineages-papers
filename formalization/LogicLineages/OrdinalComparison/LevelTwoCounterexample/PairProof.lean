module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSemanticStatementChecks
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionRealizationProof

public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairProof
open PolynomialGraphCompletion
open PolynomialGraphCompletion.ExpressionSupportProof
open PolynomialGraphCompletion.ExpressionNodeProof
open PolynomialGraphCompletion.ExpressionRealizationProof

/-- A finite natural prefix changes only the listed names, for an arbitrary
matrix. In particular this does not impose positivity on auxiliary nodes. -/
theorem existsPrefix_iff_frame (ν : Nat → Nat) (xs : List Nat)
    (body : (Nat → Nat) → Prop) :
    Pair.existsPrefix ν xs body ↔ ∃ σ : Nat → Nat,
      (∀ i, i ∉ xs → σ i = ν i) ∧ body σ := by
  induction xs generalizing ν with
  | nil =>
      constructor
      · intro h
        exact ⟨ν,fun _ _ => rfl,h⟩
      · rintro ⟨σ,hframe,h⟩
        have he : σ = ν := funext (fun i => hframe i (by simp))
        subst σ
        exact h
  | cons j xs ih =>
      constructor
      · rintro ⟨n,hn⟩
        obtain ⟨σ,hframe,h⟩ := (ih (Function.update ν j n)).mp hn
        refine ⟨σ,?_,h⟩
        intro i hi
        have hix : i ∉ xs := fun hm => hi (List.mem_cons_of_mem j hm)
        have hij : i ≠ j := by
          intro he
          apply hi
          simp only [List.mem_cons,he,true_or]
        rw [hframe i hix,Function.update_of_ne hij]
      · rintro ⟨σ,hframe,h⟩
        refine ⟨σ j,(ih (Function.update ν j (σ j))).mpr ⟨σ,?_,h⟩⟩
        intro i hi
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
        · rw [Function.update_of_ne hij]
          apply hframe i
          simp only [List.mem_cons,not_or]
          exact ⟨hij,hi⟩

private theorem valid_pair {a b : Expr} (ha : ValidExpr a) (hb : ValidExpr b) :
    ValidExpr (.add a b) := by
  intro code hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ha code hc
  · exact hb code hc

private theorem fresh_pair {n : Nat} {a b : Expr} (ha : Fresh n a) (hb : Fresh n b) :
    Fresh n (.add a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem difference_domain (x y : Nat) (ν : Nat → Nat) :
    RowDomain (Pair.differenceRow x y) ν := variable_domain x y ν

theorem difference_allowed (D x y : Nat) :
    RowAllowed D (Pair.differenceRow x y) := variable_allowed D x y

theorem difference_value (x y : Nat) (ν : Nat → Nat) :
    RowValue (Pair.differenceRow x y) ν = (ν x : Int) - (ν y : Int) := by
  simp only [Pair.differenceRow,RowValue,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,wordValue,one_mul,neg_one_mul,add_zero,zero_add,sub_eq_add_neg]

theorem badSign_iff_not_relation (mode a b : Nat) :
    Pair.badSign mode ((a : Int) - (b : Int)) ↔ ¬Pair.valueRelation mode a b := by
  unfold Pair.badSign Pair.valueRelation
  split_ifs <;> omega

theorem failed_comparison (mode a b : Nat) (flag : Bool) :
    (flag = false ∨ Pair.badSign mode ((a : Int) - (b : Int))) ↔
      ¬(flag = true ∧ Pair.valueRelation mode a b) := by
  rw [badSign_iff_not_relation]
  cases flag <;> simp

/-- Soundness is applied separately to the two child graphs, both at the
same valuation. The auxiliary sum node is never the compared value. -/
theorem difference_value_of_graph (n : Nat) (a b : Expr)
    (ha : ValidExpr a) (hb : ValidExpr b) (ν : Nat → Nat)
    (hgraph : GraphHolds n (.add a b) ν) :
    RowValue (Pair.differenceRow (output n a) (output (n+nodeCount a) b)) ν =
      (a.value ν : Int) - (b.value ν : Int) := by
  obtain ⟨hga,hgb,_⟩ := (graph_add n a b ν).mp hgraph
  rw [difference_value,
    ExpressionSemanticStatementChecks.graph_soundness n a ha ν hga,
    ExpressionSemanticStatementChecks.graph_soundness (n+nodeCount a) b hb ν hgb]

theorem exactCounterexample : PairTargets.ExactCounterexample := by
  intro n mode flag a b ha hb hfa hfb
  unfold Pair.Closed
  rw [existsPrefix_iff_frame]
  constructor
  · rintro ⟨ν,_,hmatrix⟩
    have hgraph : GraphHolds n (.add a b) ν := hmatrix.2.1
    have hbad : flag = false ∨ Pair.badSign mode
        (RowValue (Pair.differenceRow (output n a) (output (n+nodeCount a) b)) ν) :=
      hmatrix.2.2.2
    rw [difference_value_of_graph n a b ha hb ν hgraph] at hbad
    exact ⟨ν,hmatrix.1,(failed_comparison mode (a.value ν) (b.value ν) flag).mp hbad⟩
  · rintro ⟨ν,hpositive,hbad⟩
    let μ : Nat → Nat := fun i => if i < n then ν i else 0
    have hμ (i : Nat) (hi : i < n) : μ i = ν i := by
      simp only [μ,if_pos hi]
    obtain ⟨σ,hframe,hgraph,_⟩ :=
      ExpressionSemanticStatementChecks.total_graph_realization n (.add a b)
        (valid_pair ha hb) μ (fresh_pair hfa hfb)
    have horiginal (i : Nat) (hi : i < n) : σ i = ν i := by
      rw [hframe i (not_allocated_below n (.add a b) i hi)]
      exact hμ i hi
    have hva : a.value σ = a.value ν :=
      source_value_congr a σ ν (fun i hi => horiginal i (hfa i hi))
    have hvb : b.value σ = b.value ν :=
      source_value_congr b σ ν (fun i hi => horiginal i (hfb i hi))
    refine ⟨σ,?_,?_⟩
    · intro i hi
      have hbound : ¬i < n+nodeCount (.add a b) := by
        simpa only [Pair.package,List.mem_range] using hi
      have hnot : i ∉ allocated n (.add a b) := by
        intro hm
        exact hbound ((mem_allocated n (.add a b) i).mp hm).2
      have hin : ¬i < n := by omega
      rw [hframe i hnot]
      simp only [μ,if_neg hin]
    · change (∀ i < n, 0 < σ i) ∧ RowsHold (rows n (.add a b)) σ ∧
        RowDomain (Pair.differenceRow (output n a) (output (n+nodeCount a) b)) σ ∧
        (flag = false ∨ Pair.badSign mode
          (RowValue (Pair.differenceRow (output n a) (output (n+nodeCount a) b)) σ))
      refine ⟨?_,hgraph,difference_domain _ _ σ,?_⟩
      · intro i hi
        rw [horiginal i hi]
        exact hpositive i hi
      · rw [difference_value_of_graph n a b ha hb σ hgraph,hva,hvb]
        exact (failed_comparison mode (a.value ν) (b.value ν) flag).mpr hbad

theorem exactClosedSupport : PairTargets.ExactClosedSupport := by
  intro n mode flag a b hfa hfb
  change (List.range (n+nodeCount (.add a b))).Nodup ∧
    List.range (n+nodeCount (.add a b)) = List.range (n+nodeCount (.add a b)) ∧
    (∀ row ∈ rows n (.add a b), ∀ i ∈ rowVariables row,
      i ∈ List.range (n+nodeCount (.add a b))) ∧
    (∀ i ∈ rowVariables (Pair.differenceRow (output n a) (output (n+nodeCount a) b)),
      i ∈ List.range (n+nodeCount (.add a b))) ∧
    (∀ i < n, i ∉ allocated n (.add a b))
  refine ⟨List.nodup_range,rfl,?_,?_,?_⟩
  · intro row hr i hi
    apply List.mem_range.mpr
    rcases rows_support n (.add a b) row hr i hi with hs | hn
    · have h := fresh_pair hfa hfb i hs
      omega
    · exact ((mem_allocated n (.add a b) i).mp hn).2
  · intro i hi
    have he : i = output n a ∨ i = output (n+nodeCount a) b := by
      simpa [rowVariables,Pair.differenceRow] using hi
    apply List.mem_range.mpr
    rcases he with rfl | rfl
    · have h := (mem_allocated n a (output n a)).mp (output_mem_allocated n a)
      simp only [nodeCount]
      omega
    · have h := (mem_allocated (n+nodeCount a) b (output (n+nodeCount a) b)).mp
        (output_mem_allocated (n+nodeCount a) b)
      simp only [nodeCount]
      omega
  · exact fun i hi => not_allocated_below n (.add a b) i hi

theorem exactDomainsAndDegree : PairTargets.ExactDomainsAndDegree := by
  intro n mode flag a b ha hb
  have h := ExpressionSemanticStatementChecks.expression_domains_and_degree
    (.add a b) (valid_pair ha hb)
  change 3 ≤ exprDegree (.add a b) ∧
    (∀ row ∈ rows n (.add a b), RowAllowed (exprDegree (.add a b)) row ∧
      ∀ ν, RowDomain row ν) ∧
    RowAllowed (exprDegree (.add a b))
      (Pair.differenceRow (output n a) (output (n+nodeCount a) b)) ∧
    ∀ ν, RowDomain (Pair.differenceRow (output n a) (output (n+nodeCount a) b)) ν
  exact ⟨h.1,fun row hr => h.2.1 n row hr,difference_allowed _ _ _,difference_domain _ _⟩

end LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairProof
