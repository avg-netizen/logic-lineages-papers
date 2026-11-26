module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsTargets
import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsBuildProof
import LogicLineages.PermittedControl.FunnelProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotations
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue

private theorem linearNotNonlinear (op : LowerOperand)
    (linear : LinearOperand op) (nonlinear : NonlinearOperand op) : False := by
  cases op with
  | coordinate rank => exact nonlinear
  | count rank lam mu => exact linear
  | ordinary rank F =>
      cases F with
      | iterate k =>
          cases k with
          | zero => exact Nat.lt_irrefl 0 nonlinear
          | succ k => exact linear
      | entry k lam mu => exact linear

private theorem annotatedImage (f : Nat → Nat) (ρ : Nat → Nat)
    (monotone : Monotone f) (t : WeightedOperand) (v : Nat) (ann : Annotation)
    (actual : ActualAnnotation f ρ t v ann) (weight : t.1 ≠ 0)
    (nonlinear : NonlinearOperand t.2) :
    ∃ D, fullValue f ann = some D ∧ f (ρ t.2.rank) ≤ D := by
  cases ann with
  | zeroWeight => exact False.elim (weight actual)
  | linear => exact False.elim (linearNotNonlinear t.2 actual.2.1 nonlinear)
  | ordinary q =>
      obtain ⟨_,rank,F,op,_,bound,_⟩ := actual
      refine ⟨f q,rfl,?_⟩
      rw [op]
      exact monotone bound
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,op,_,_,_,_,bound,_⟩ := actual
      refine ⟨f q,rfl,?_⟩
      rw [op]
      exact monotone ((Nat.le_add_right _ _).trans bound)

private theorem assignedImage (f : Nat → Nat) (ρ : Nat → Nat) (monotone : Monotone f)
    {terms : List WeightedOperand} {values : List Nat} {annotations : List Annotation}
    (aligned : AlignedAnnotations f ρ terms values annotations)
    (t : WeightedOperand) (member : t ∈ terms) (weight : t.1 ≠ 0)
    (nonlinear : NonlinearOperand t.2) :
    ∃ D, D ∈ fullValues f annotations ∧ f (ρ t.2.rank) ≤ D := by
  induction aligned with
  | nil => exact False.elim (List.not_mem_nil member)
  | @cons head terms value values ann annotations _ _ actual _ next =>
      rcases List.mem_cons.mp member with equal | tail
      · subst t
        obtain ⟨D,image,bound⟩ := annotatedImage f ρ monotone head value ann actual weight nonlinear
        exact ⟨D,List.mem_filterMap.mpr ⟨ann,List.mem_cons_self,image⟩,bound⟩
      · obtain ⟨D,found,bound⟩ := next tail
        obtain ⟨other,inTail,image⟩ := List.mem_filterMap.mp found
        exact ⟨D,List.mem_filterMap.mpr ⟨other,List.mem_cons_of_mem _ inTail,image⟩,bound⟩

theorem largestActualFull : LargestActualFull := by
  intro f B selected ρ zRank terms values reads ready _ active
  obtain ⟨annotations,aligned⟩ := buildActualAnnotations f B selected ρ terms values reads ready
  obtain ⟨t,member,weight,atRank,nonlinear⟩ := active
  have monotone := (selected_threshold_admissible f B selected).1.monotone
  obtain ⟨D,found,bound⟩ := assignedImage f ρ monotone aligned t member weight nonlinear
  cases maximum : (fullValues f annotations).max? with
  | none =>
      have empty := List.max?_eq_none_iff.mp maximum
      rw [empty] at found
      exact False.elim (List.not_mem_nil found)
  | some C =>
      have exactMax := List.max?_eq_some_iff.mp maximum
      rw [atRank] at bound
      exact ⟨annotations,C,aligned,maximum,exactMax.1,exactMax.2,
        bound.trans (exactMax.2 D found)⟩

end LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotations
