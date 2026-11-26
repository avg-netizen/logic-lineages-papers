module
public import LogicLineages.PermittedControl.ActualRankedZeroClassTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRankedZeroClass
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualRankedRowColumns

theorem distinctColumns {r : Nat} (v : ValueKey r) (n : CountKey r) :
    valueOperand r v ≠ countOperand r n := by
  intro same
  change LowerOperand.ordinary v.1 v.2 = .count n.2 n.1.1 n.1.2 at same
  cases same

def KeyFacts {r : Nat} (row : RankedRow r) (rd : Read) : ValueKey r ⊕ CountKey r → Prop
  | .inl k => rd.1.2 = valueOperand r k ∧ k ∈ row.value.support ∧
      leadingWeight rd = 2 * row.value k
  | .inr k => rd.1.2 = countOperand r k ∧ k ∈ row.count.support ∧
      leadingWeight rd = row.count k

theorem chargedKey {r : Nat} (row : RankedRow r) (rd : Read)
    (charged : NonlinearOperand rd.1.2) (inColumn : IsInRankedColumn row rd) :
    ∃ key, finiteClassKey r rd.1.2 = some key ∧ KeyFacts row rd key := by
  cases shape : rd.1.2 with
  | coordinate n =>
      exact False.elim (by simpa only [shape,NonlinearOperand] using charged)
  | ordinary n F =>
      simp only [IsInRankedColumn,shape] at inColumn
      have active : SelectedNonlinearImageBounds.NonlinearField F := by
        simpa only [NonlinearOperand,shape] using charged
      obtain ⟨i,rank,member,weight⟩ := inColumn active
      have bound : n < r := rank ▸ i.isLt
      refine ⟨.inl (i,F),?_,?_,member,?_⟩
      · rw [shape]
        simp only [finiteClassKey,dif_pos bound,Option.some.injEq,Sum.inl.injEq]
        exact Prod.ext (Fin.ext rank.symm) rfl
      · rw [shape]
        change LowerOperand.ordinary n F = .ordinary i.1 F
        rw [rank]
      · simp only [leadingWeight,shape,weight]
  | count n lam mu =>
      simp only [IsInRankedColumn,shape] at inColumn
      obtain ⟨i,rank,member,weight⟩ := inColumn
      have bound : n < r := rank ▸ i.isLt
      refine ⟨.inr ((lam,mu),i),?_,?_,member,?_⟩
      · rw [shape]
        simp only [finiteClassKey,dif_pos bound,Option.some.injEq,Sum.inr.injEq]
        exact Prod.ext rfl (Fin.ext rank.symm)
      · rw [shape]
        change LowerOperand.count n lam mu = .count i.1 lam mu
        rw [rank]
      · simp only [leadingWeight,shape,weight]

private theorem insertMember {α : Type} [DecidableEq α] (embed : α ↪ LowerOperand)
    (old : Finset α) (xs : List Read) (rd : Read) (head : α)
    (base : ∀ k, k ∈ old ↔ ∃ prior ∈ xs, prior.1.2 = embed k)
    (known : rd.1.2 = embed head) (k : α) :
    k ∈ insert head old ↔ ∃ prior ∈ rd::xs, prior.1.2 = embed k := by
  constructor
  · intro member
    rcases Finset.mem_insert.mp member with equal | rest
    · subst k
      exact ⟨rd,List.mem_cons_self,known⟩
    · obtain ⟨prior,among,mapped⟩ := (base k).mp rest
      exact ⟨prior,List.mem_cons_of_mem _ among,mapped⟩
  · rintro ⟨prior,among,mapped⟩
    rcases List.mem_cons.mp among with equal | tail
    · subst prior
      have same : k = head := embed.injective (mapped.symm.trans known)
      exact Finset.mem_insert.mpr (.inl same)
    · exact Finset.mem_insert.mpr (.inr ((base k).mpr ⟨prior,tail,mapped⟩))

private theorem skipMember {α : Type} (embed : α ↪ LowerOperand)
    (old : Finset α) (xs : List Read) (rd : Read)
    (base : ∀ k, k ∈ old ↔ ∃ prior ∈ xs, prior.1.2 = embed k)
    (different : ∀ k, rd.1.2 ≠ embed k) (k : α) :
    k ∈ old ↔ ∃ prior ∈ rd::xs, prior.1.2 = embed k := by
  constructor
  · intro member
    obtain ⟨prior,among,mapped⟩ := (base k).mp member
    exact ⟨prior,List.mem_cons_of_mem _ among,mapped⟩
  · rintro ⟨prior,among,mapped⟩
    rcases List.mem_cons.mp among with equal | tail
    · subst prior
      exact False.elim (different k mapped)
    · exact (base k).mpr ⟨prior,tail,mapped⟩

private theorem freshKey {α : Type} (embed : α ↪ LowerOperand)
    (old : Finset α) (xs : List Read) (rd : Read) (head : α)
    (base : ∀ k, k ∈ old ↔ ∃ prior ∈ xs, prior.1.2 = embed k)
    (known : rd.1.2 = embed head) (fresh : rd.1.2 ∉ xs.map (fun p => p.1.2)) : head ∉ old := by
  intro member
  obtain ⟨prior,among,mapped⟩ := (base head).mp member
  exact fresh (List.mem_map.mpr ⟨prior,among,mapped.trans known.symm⟩)

theorem finiteClassFacts {r : Nat} (row : RankedRow r) (xs : List Read)
    (unique : (xs.map (fun rd => rd.1.2)).Nodup)
    (actual : ∀ rd ∈ xs, NonlinearOperand rd.1.2 ∧ IsInRankedColumn row rd) :
    let cols := finiteClassColumns r xs
    (∀ k : ValueKey r, k ∈ cols.1 ↔ ∃ rd ∈ xs, rd.1.2 = valueOperand r k) ∧
    (∀ k : CountKey r, k ∈ cols.2 ↔ ∃ rd ∈ xs, rd.1.2 = countOperand r k) ∧
    (xs.map leadingWeight).sum = 2 * (∑ k ∈ cols.1, row.value k) + ∑ k ∈ cols.2, row.count k := by
  classical
  induction xs with
  | nil => simp [finiteClassColumns]
  | cons rd xs next =>
      change (rd.1.2 :: xs.map (fun p => p.1.2)).Nodup at unique
      obtain ⟨fresh,tailUnique⟩ := List.nodup_cons.mp unique
      obtain ⟨values,counts,sum⟩ :=
        next tailUnique (fun p among => actual p (List.mem_cons_of_mem _ among))
      obtain ⟨key,found,facts⟩ := chargedKey row rd
        (actual rd List.mem_cons_self).1 (actual rd List.mem_cons_self).2
      let tail := finiteClassColumns r xs
      cases key with
      | inl k =>
          obtain ⟨origin,member,weight⟩ := facts
          have newKey := freshKey (valueOperand r) tail.1 xs rd k values origin fresh
          simp only [finiteClassColumns,found,List.map_cons,List.sum_cons]
          refine ⟨insertMember (valueOperand r) tail.1 xs rd k values origin,
            skipMember (countOperand r) tail.2 xs rd counts (fun n same =>
              distinctColumns k n (origin.symm.trans same)),?_⟩
          rw [weight,sum,Finset.sum_insert newKey,mul_add]
          ac_rfl
      | inr k =>
          obtain ⟨origin,member,weight⟩ := facts
          have newKey := freshKey (countOperand r) tail.2 xs rd k counts origin fresh
          simp only [finiteClassColumns,found,List.map_cons,List.sum_cons]
          refine ⟨skipMember (valueOperand r) tail.1 xs rd values (fun v same =>
              distinctColumns v k (same.symm.trans origin)),
            insertMember (countOperand r) tail.2 xs rd k counts origin,?_⟩
          rw [weight,sum,Finset.sum_insert newKey]
          ac_rfl

end LogicLineages.PermittedControl.ActualRankedZeroClass
