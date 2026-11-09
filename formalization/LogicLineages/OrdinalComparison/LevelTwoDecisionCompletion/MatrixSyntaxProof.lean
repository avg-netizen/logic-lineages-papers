module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixRowsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open LogicLineages.ModelsAlgebra.Forests

theorem positiveFold_tokens (xs : List Nat) :
    Formula.tokens (xs.foldr
      (fun i p => .conj (.atom (.nonnegative (positiveRow i))) p) .top) =
      xs.map (fun i => (i,([] : Word))) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldr_cons,tokens_conjunction]
      rw [ih]
      rfl

theorem positiveFrame_tokens (n : Nat) :
    (positiveFrame n).tokens = (List.range n).map (fun i => (i,([] : Word))) :=
  positiveFold_tokens (List.range n)

theorem rowEquation_tokens (r : Row) (t : Token) :
    t ∈ (rowEquation r).tokens ↔ t ∈ r.2.map Prod.snd := by
  simp [rowEquation]

theorem rowEquations_tokens (rs : List Row) (t : Token) :
    t ∈ (rowEquations rs).tokens ↔ ∃ r ∈ rs, t ∈ r.2.map Prod.snd := by
  induction rs with
  | nil => simp [rowEquations,Formula.tokens,CotreePresburgerUnit.Boolean.atoms]
  | cons r rs ih =>
      change t ∈ Formula.tokens (.conj (rowEquation r) (rowEquations rs)) ↔ _
      rw [tokens_conjunction,List.mem_append,rowEquation_tokens]
      constructor
      · rintro (hr | hrs)
        · exact ⟨r,List.mem_cons_self,hr⟩
        · obtain ⟨s,hs,ht⟩ := ih.mp hrs
          exact ⟨s,List.mem_cons_of_mem r hs,ht⟩
      · rintro ⟨s,hs,ht⟩
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inl ht
        · exact Or.inr (ih.mpr ⟨s,hs,ht⟩)

theorem badSign_tokens (mode : Nat) (r : Row) (t : Token) :
    t ∈ (badSignFormula mode r).tokens ↔ t ∈ r.2.map Prod.snd := by
  unfold badSignFormula
  split_ifs <;> simp [rowEquation]

theorem failedPositive_tokens (flag : Bool) : (failedPositive flag).tokens = [] := by
  cases flag <;> rfl

/-- Every actual token comes from an original coordinate, a graph row or the
comparison row. The last source is retained even under a true first disjunct. -/
theorem matrix_tokens_property (p : Pair.Package) (P : Token → Prop)
    (hpositive : ∀ i < p.1.2, P (i,[]))
    (hrows : ∀ r ∈ p.2.2.1, ∀ t ∈ r.2.map Prod.snd, P t)
    (hcomparison : ∀ t ∈ p.2.2.2.1.2.map Prod.snd, P t) :
    ∀ t ∈ (matrix p).tokens, P t := by
  intro t ht
  have hm : t ∈ (positiveFrame p.1.2).tokens ∨
      t ∈ (rowEquations p.2.2.1).tokens ∨
      t ∈ (badSignFormula p.2.2.2.2.1 p.2.2.2.1).tokens := by
    simpa only [matrix,tokens_conjunction,tokens_disjunction,failedPositive_tokens,
      List.nil_append,List.mem_append] using ht
  rcases hm with hp | hr | hc
  · rw [positiveFrame_tokens] at hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact hpositive i (List.mem_range.mp hi)
  · obtain ⟨r,hr,ht⟩ := (rowEquations_tokens _ _).mp hr
    exact hrows r hr t ht
  · exact hcomparison t ((badSign_tokens _ _ _).mp hc)

theorem exactMatrixSyntax : Targets.ExactMatrixSyntax := by
  intro p hp
  constructor
  · apply matrix_tokens_property p (fun t => WordAllowed p.1.1 t.2)
    · intro i hi
      simp [WordAllowed]
    · intro r hr t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      exact (hp.2.2.2.1 r hr).1 s hs
    · intro t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      exact hp.2.2.2.2.1 s hs
  · intro i hi
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
    apply matrix_tokens_property p (fun t => t.1 ∈ p.2.1) ?_ ?_ ?_ t ht
    · exact hp.2.2.1
    · intro r hr t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      exact (hp.2.2.2.1 r hr).2 s.2.1 (List.mem_map.mpr ⟨s,hs,rfl⟩)
    · intro t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      exact hp.2.2.2.2.2 s.2.1 (List.mem_map.mpr ⟨s,hs,rfl⟩)

#print axioms positiveFold_tokens
#print axioms positiveFrame_tokens
#print axioms rowEquation_tokens
#print axioms rowEquations_tokens
#print axioms badSign_tokens
#print axioms failedPositive_tokens
#print axioms matrix_tokens_property
#print axioms exactMatrixSyntax

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MatrixProof
