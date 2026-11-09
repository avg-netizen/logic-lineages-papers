module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion

/-- Restoring a fixed original raw name does not change any other word input. -/
theorem specialize_satisfiable (floor x n : Nat) (p : Formula) (hn : floor ≤ n) :
    (OriginalWordEvaluation.removedDomains x n p = true ∧
      SatisfiableAt floor (OriginalWordEvaluation.specialize x n p)) ↔
    ∃ ν : Nat → Nat, (∀ i ∈ p.variables, floor ≤ ν i) ∧
      Formula.meaningful p ν ∧ Formula.eval ν p ∧ ν x = n := by
  constructor
  · rintro ⟨hremoved,ν,hfloor,hdomains,htrue⟩
    refine ⟨Function.update ν x n,?_,?_,?_,Function.update_self x n ν⟩
    · intro i hi
      by_cases hx : i = x
      · simpa [hx] using hn
      · rw [Function.update_of_ne hx]
        exact hfloor i ((specialized_names x n p i).mpr ⟨hx,hi⟩)
    · exact (OriginalWordEvaluation.Proof.formulaSubstitution x n p ν).2.mpr
        ⟨hremoved,hdomains⟩
    · exact (OriginalWordEvaluation.Proof.formulaSubstitution x n p ν).1.mp htrue
  · rintro ⟨ν,hfloor,hdomains,htrue,hx⟩
    have hu : Function.update ν x n = ν := by
      funext i
      by_cases hi : i = x
      · simp [hi,hx]
      · simp [Function.update_of_ne hi]
    have hsub := OriginalWordEvaluation.Proof.formulaSubstitution x n p ν
    rw [hu] at hsub
    refine ⟨(hsub.2.mp hdomains).1,ν,?_,(hsub.2.mp hdomains).2,hsub.1.mpr htrue⟩
    intro i hi
    exact hfloor i ((specialized_names x n p i).mp hi).2

/-- Exactly the finite alternatives below N, restricted to the inherited
floor and evaluated in the ORIGINAL current matrix before tail rewriting. -/
theorem prefix_equivalence (floor N : Nat) (p : Formula) :
    (∃ b ∈ prefixChildren floor N p, SatisfiableAt b.1 b.2) ↔
    ∃ ν : Nat → Nat, (∀ i ∈ p.variables, floor ≤ ν i) ∧
      Formula.meaningful p ν ∧ Formula.eval ν p ∧
      ∃ x ∈ names p, ν x < N := by
  constructor
  · rintro ⟨b,hb,htrue⟩
    obtain ⟨x,hx,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,hk,he⟩ := List.mem_filterMap.mp hb
    dsimp only at he
    split at he
    next hdom =>
      have he' : (floor,OriginalWordEvaluation.specialize x (floor+k) p) = b :=
        Option.some.inj he
      subst b
      obtain ⟨ν,hfloor,hdomains,hvalue,hxvalue⟩ :=
        (specialize_satisfiable floor x (floor+k) p (by omega)).mp ⟨hdom,htrue⟩
      refine ⟨ν,hfloor,hdomains,hvalue,x,hx,?_⟩
      have hk' := List.mem_range.mp hk
      omega
    next hdom => contradiction
  · rintro ⟨ν,hfloor,hdomains,htrue,x,hx,hsmall⟩
    have hlow := hfloor x (List.mem_dedup.mp hx)
    obtain ⟨hremoved,hchild⟩ :=
      (specialize_satisfiable floor x (ν x) p hlow).mpr
        ⟨ν,hfloor,hdomains,htrue,rfl⟩
    refine ⟨(floor,OriginalWordEvaluation.specialize x (ν x) p),?_,hchild⟩
    apply List.mem_flatMap.mpr
    refine ⟨x,hx,List.mem_filterMap.mpr ⟨ν x-floor,?_,?_⟩⟩
    · apply List.mem_range.mpr
      omega
    · have he : floor+(ν x-floor) = ν x := by omega
      simp only [he,hremoved,if_true]

/-- Maximum selection uses the finite ORIGINAL raw-name list, never word
values or a generated label history. -/
theorem exists_maximum (ns : List Nat) (hne : ns ≠ []) (ν : Nat → Nat) :
    ∃ x ∈ ns, ∀ i ∈ ns, ν i ≤ ν x := by
  induction ns with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
      by_cases hempty : xs = []
      · subst xs
        refine ⟨x,List.mem_cons_self,?_⟩
        intro i hi
        have hi' : i = x := by simpa using hi
        subst i
        exact Nat.le_refl _
      · obtain ⟨y,hy,hmax⟩ := ih hempty
        by_cases hxy : ν x ≤ ν y
        · refine ⟨y,List.mem_cons_of_mem x hy,?_⟩
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hxy
          · exact hmax i hi
        · refine ⟨x,List.mem_cons_self,?_⟩
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Nat.le_refl _
          · exact (hmax i hi).trans (by omega)

#print axioms specialize_satisfiable
#print axioms prefix_equivalence
#print axioms exists_maximum

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProof
