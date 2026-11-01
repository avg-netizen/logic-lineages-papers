module
public import LogicLineages.OrdinalComparison.PositiveSourceHeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PositiveSourceDomain

private theorem step_primitive : Primrec (fun p : Nat × List (Nat × Nat) =>
    encodedPositiveSourceDataStep p.1 p.2) := by
  have hn : Primrec (fun p : Nat × List (Nat × Nat) => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat × List (Nat × Nat) => p.2) := Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 4))
  have hl := (Primrec.list_getD (0,0)).comp ht (Primrec.fst.comp hp)
  have hr := (Primrec.list_getD (0,0)).comp ht (Primrec.snd.comp hp)
  have hvl := Primrec.eq.comp (Primrec.fst.comp hl) (Primrec.const 1)
  have hvr := Primrec.eq.comp (Primrec.fst.comp hr) (Primrec.const 1)
  have hil := Primrec.eq.comp (Primrec.snd.comp hl) (Primrec.const 1)
  have hir := Primrec.eq.comp (Primrec.snd.comp hr) (Primrec.const 1)
  have hadv := Primrec.ite (hvl.and hvr) (Primrec.const 1) (Primrec.const 0)
  have hadi := Primrec.ite (hil.or hir) (Primrec.const 1) (Primrec.const 0)
  have hhead := Primrec.eq.comp (head_domain_primitive.comp (Primrec.fst.comp hp)) (Primrec.const 1)
  have hhv := Primrec.ite (hhead.and hvr) (Primrec.const 1) (Primrec.const 0)
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const (1,0))
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp hn (Primrec.const 1)) (Primrec.const (1,1)) (Primrec.const (0,0)))
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2)) (hadv.pair hadi) (hhv.pair (Primrec.snd.comp hr))))

theorem data_primitive : Primrec encodedPositiveSourceData := by
  have hs : Primrec₂ (fun n : Nat => fun table : List (Nat × Nat) =>
      table ++ [encodedPositiveSourceDataStep n table]) :=
    Primrec.list_concat.comp Primrec.snd step_primitive
  have ht : Primrec encodedPositiveSourceDataTable :=
    (Primrec.nat_rec₁ ([] : List (Nat × Nat)) hs).of_eq (by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List (Nat × Nat)) []
          (fun k table => table ++ [encodedPositiveSourceDataStep k table]) n ++
          [encodedPositiveSourceDataStep n (Nat.rec (motive := fun _ => List (Nat × Nat)) []
            (fun k table => table ++ [encodedPositiveSourceDataStep k table]) n)] = _
        change Nat.rec (motive := fun _ => List (Nat × Nat)) []
          (fun k table => table ++ [encodedPositiveSourceDataStep k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD (0,0)).comp (ht.comp Primrec.succ) Primrec.id

theorem table_length (n : Nat) : (encodedPositiveSourceDataTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedPositiveSourceDataTable,ih]

theorem data_equation (n : Nat) : encodedPositiveSourceData n=
    encodedPositiveSourceDataStep n (encodedPositiveSourceDataTable n) := by
  unfold encodedPositiveSourceData
  rw [encodedPositiveSourceDataTable,List.getD_append_right _ _ _ _ (by rw [table_length])]
  simp only [table_length,Nat.sub_self,List.getD_cons_zero]

theorem table_correct (n : Nat) : ∀ i : Nat, i<n →
    (encodedPositiveSourceDataTable n).getD i (0,0)=encodedPositiveSourceData i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases hin : i<n
    · rw [encodedPositiveSourceDataTable,List.getD_append _ _ _ _ (by rw [table_length]; exact hin)]
      exact ih i hin
    · have heq : i=n := by omega
      subst i
      rw [encodedPositiveSourceDataTable,List.getD_append_right _ _ _ _ (by rw [table_length])]
      simp only [table_length,Nat.sub_self,List.getD_cons_zero]
      exact (data_equation n).symm

end LogicLineages.OrdinalComparison.PositiveSourceDomain
