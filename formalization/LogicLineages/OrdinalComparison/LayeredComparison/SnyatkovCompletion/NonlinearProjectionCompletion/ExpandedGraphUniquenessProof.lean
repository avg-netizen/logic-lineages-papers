module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphSoundnessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
open ExpandedGraph

theorem graph_output_unique (start : Nat) (t : Term) (ν σ : Nat → Nat)
    (ht : PlainBlockSplit.termHFree t = true)
    (hsource : ∀ i ∈ t.variables, ν i = σ i)
    (hν : (graph start t).eval ν) (hσ : (graph start t).eval σ) :
    ν (output start t) = σ (output start t) :=
  (graphSoundness start t ν ht hν).trans
    ((term_value_congr t ν σ hsource).trans (graphSoundness start t σ ht hσ).symm)

theorem allocatedNodeUniqueness : ExpandedGraphTargets.AllocatedNodeUniqueness := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ν σ ht hsource hν hσ i hi
      have hb := (mem_allocated start (.numeral n) i).mp hi
      have he : i = output start (.numeral n) := by
        simp only [nodeCount] at hb
        simp only [output, nodeCount]
        omega
      rw [he]
      exact graph_output_unique start (.numeral n) ν σ ht hsource hν hσ
  | «variable» j =>
      intro ν σ ht hsource hν hσ i hi
      have hb := (mem_allocated start (.variable j) i).mp hi
      have he : i = output start (.variable j) := by
        simp only [nodeCount] at hb
        simp only [output, nodeCount]
        omega
      rw [he]
      exact graph_output_unique start (.variable j) ν σ ht hsource hν hσ
  | add a b iha ihb =>
      intro ν σ ht hsource hν hσ i hi
      have hta := (Bool.and_eq_true_iff.mp ht).1
      have htb := (Bool.and_eq_true_iff.mp ht).2
      have hsourceA : ∀ j ∈ a.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_left _ hj)
      have hsourceB : ∀ j ∈ b.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_right _ hj)
      obtain ⟨haν, hbν, _⟩ := (graph_add start a b ν).mp hν
      obtain ⟨haσ, hbσ, _⟩ := (graph_add start a b σ).mp hσ
      have hi' := (mem_allocated start (.add a b) i).mp hi
      simp only [nodeCount] at hi'
      by_cases hia : i < start + nodeCount a
      · apply iha start ν σ hta hsourceA haν haσ i
        exact (mem_allocated start a i).mpr ⟨hi'.1, hia⟩
      · by_cases hib : i < start + nodeCount a + nodeCount b
        · apply ihb (start + nodeCount a) ν σ htb hsourceB hbν hbσ i
          apply (mem_allocated (start + nodeCount a) b i).mpr
          constructor <;> omega
        · have he : i = output start (.add a b) := by
            simp only [output, nodeCount]
            omega
          rw [he]
          exact graph_output_unique start (.add a b) ν σ ht hsource hν hσ
  | subtract a b iha ihb =>
      intro ν σ ht hsource hν hσ i hi
      have hta := (Bool.and_eq_true_iff.mp ht).1
      have htb := (Bool.and_eq_true_iff.mp ht).2
      have hsourceA : ∀ j ∈ a.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_left _ hj)
      have hsourceB : ∀ j ∈ b.variables, ν j = σ j :=
        fun j hj => hsource j (List.mem_append_right _ hj)
      obtain ⟨haν, hbν, _⟩ := (graph_subtract start a b ν).mp hν
      obtain ⟨haσ, hbσ, _⟩ := (graph_subtract start a b σ).mp hσ
      have hi' := (mem_allocated start (.subtract a b) i).mp hi
      simp only [nodeCount] at hi'
      by_cases hia : i < start + nodeCount a
      · apply iha start ν σ hta hsourceA haν haσ i
        exact (mem_allocated start a i).mpr ⟨hi'.1, hia⟩
      · by_cases hib : i < start + nodeCount a + nodeCount b
        · apply ihb (start + nodeCount a) ν σ htb hsourceB hbν hbσ i
          apply (mem_allocated (start + nodeCount a) b i).mpr
          constructor <;> omega
        · have he : i = output start (.subtract a b) := by
            simp only [output, nodeCount]
            omega
          rw [he]
          exact graph_output_unique start (.subtract a b) ν σ ht hsource hν hσ
  | multiply c a ih =>
      intro ν σ ht hsource hν hσ i hi
      obtain ⟨haν, _⟩ := (graph_multiply start c a ν).mp hν
      obtain ⟨haσ, _⟩ := (graph_multiply start c a σ).mp hσ
      have hi' := (mem_allocated start (.multiply c a) i).mp hi
      simp only [nodeCount] at hi'
      by_cases hia : i < start + nodeCount a
      · exact ih start ν σ ht hsource haν haσ i ((mem_allocated start a i).mpr ⟨hi'.1, hia⟩)
      · have he : i = output start (.multiply c a) := by
          simp only [output, nodeCount]
          omega
        rw [he]
        exact graph_output_unique start (.multiply c a) ν σ ht hsource hν hσ
  | divide c a ih =>
      intro ν σ ht hsource hν hσ i hi
      obtain ⟨haν, _⟩ := (graph_divide start c a ν).mp hν
      obtain ⟨haσ, _⟩ := (graph_divide start c a σ).mp hσ
      have hi' := (mem_allocated start (.divide c a) i).mp hi
      simp only [nodeCount] at hi'
      by_cases hia : i < start + nodeCount a
      · exact ih start ν σ ht hsource haν haσ i ((mem_allocated start a i).mpr ⟨hi'.1, hia⟩)
      · have he : i = output start (.divide c a) := by
          simp only [output, nodeCount]
          omega
        rw [he]
        exact graph_output_unique start (.divide c a) ν σ ht hsource hν hσ
  | phi a ih =>
      intro ν σ ht hsource hν hσ i hi
      obtain ⟨haν, _⟩ := (graph_phi start a ν).mp hν
      obtain ⟨haσ, _⟩ := (graph_phi start a σ).mp hσ
      have hi' := (mem_allocated start (.phi a) i).mp hi
      simp only [nodeCount] at hi'
      by_cases hia : i < start + nodeCount a
      · exact ih start ν σ ht hsource haν haσ i ((mem_allocated start a i).mpr ⟨hi'.1, hia⟩)
      · have he : i = output start (.phi a) := by
          simp only [output, nodeCount]
          omega
        rw [he]
        exact graph_output_unique start (.phi a) ν σ ht hsource hν hσ
  | phiInverse a ih =>
      intro ν σ ht hsource hν hσ i hi
      obtain ⟨haν, huν, _⟩ := (graph_phiInverse start a ν).mp hν
      obtain ⟨haσ, huσ, _⟩ := (graph_phiInverse start a σ).mp hσ
      have hout := graph_output_unique start (.phiInverse a) ν σ ht hsource hν hσ
      have hi' := (mem_allocated start (.phiInverse a) i).mp hi
      simp only [nodeCount] at hi'
      by_cases hia : i < start + nodeCount a
      · exact ih start ν σ ht hsource haν haσ i ((mem_allocated start a i).mpr ⟨hi'.1, hia⟩)
      · by_cases hiu : i = start + nodeCount a
        · rw [hiu, huν, huσ, hout]
        · have he : i = output start (.phiInverse a) := by
            simp only [output, nodeCount]
            omega
          rw [he]
          exact hout
  | hyper a ih => intro ν σ ht; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at ht
  | hyperInverse a ih => intro ν σ ht; simp only [PlainBlockSplit.termHFree, Bool.false_eq_true] at ht

#print axioms graph_output_unique
#print axioms allocatedNodeUniqueness
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphProof
