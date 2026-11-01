module
public import LogicLineages.OrdinalComparison.SingleCoreSupportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreSupport

private theorem step_primitive : Primrec (fun p : Nat × List (List Nat) => encodedSingleCoreSupportStep p.1 p.2) := by
  have hm := Primrec.nat_mod.comp (Primrec.fst : Primrec (fun p : Nat × List (List Nat) => p.1)) (Primrec.const 4)
  have hd := Primrec.nat_div.comp (Primrec.fst : Primrec (fun p : Nat × List (List Nat) => p.1)) (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hL := (Primrec.list_getD []).comp Primrec.snd (Primrec.fst.comp hp)
  have hR := (Primrec.list_getD []).comp Primrec.snd (Primrec.snd.comp hp)
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1))
      (Primrec.list_cons.comp hd (Primrec.const []))
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2)) (Primrec.list_append.comp hL hR) hR))

theorem primitive : Primrec encodedSingleCoreSupport := by
  have hs : Primrec₂ (fun _ : Nat => fun state : Nat × List (List Nat) =>
      state.2++[encodedSingleCoreSupportStep state.1 state.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) (step_primitive.comp Primrec.snd)
  have ht : Primrec₂ (fun _ : Nat => encodedSingleCoreSupportTable) :=
    (Primrec.nat_rec (Primrec.const ([] : List (List Nat))) hs).of_eq (by
      intro dummy n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List (List Nat)) []
          (fun k previous => previous++[encodedSingleCoreSupportStep k previous]) n++
          [encodedSingleCoreSupportStep n (Nat.rec (motive := fun _ => List (List Nat)) []
            (fun k previous => previous++[encodedSingleCoreSupportStep k previous]) n)]=_
        rw [ih]
        rfl)
  have htable := ht.comp (Primrec.const 0) Primrec.id
  exact (Primrec.list_getD []).comp (htable.comp Primrec.succ) Primrec.id

private theorem table_length (n : Nat) : (encodedSingleCoreSupportTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodedSingleCoreSupportTable,List.length_append,List.length_singleton,ih]

private theorem step_source (E : MultivariatePositiveExpr) (table : List (List Nat))
    (ht : ∀ F : MultivariatePositiveExpr,multivariatePositiveEncode F<multivariatePositiveEncode E →
      table.getD (multivariatePositiveEncode F) []=singleCoreSupport F) :
    encodedSingleCoreSupportStep (multivariatePositiveEncode E) table=singleCoreSupport E := by
  cases E with
  | constant c => simp [multivariatePositiveEncode,encodedSingleCoreSupportStep,singleCoreSupport]
  | input i =>
    have hm : (4*i+1)%4=1 := by omega
    have hd : (4*i+1)/4=i := by omega
    simp [multivariatePositiveEncode,encodedSingleCoreSupportStep,singleCoreSupport,hm,hd]
  | add E F =>
    have hE : multivariatePositiveEncode E<4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2 :=
      lt_of_le_of_lt (Nat.left_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)) (by omega)
    have hF : multivariatePositiveEncode F<4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2 :=
      lt_of_le_of_lt (Nat.right_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)) (by omega)
    have hm : (4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2)%4=2 := by omega
    have hd : (4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2)/4=
        Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F) := by omega
    simp only [multivariatePositiveEncode,encodedSingleCoreSupportStep,hm,hd,Nat.unpair_pair,
      show ¬(2=0) from by decide,show ¬(2=1) from by decide,if_false,if_true,singleCoreSupport]
    exact congrArg₂ List.append (ht E hE) (ht F hF)
  | head rho E =>
    have hE : multivariatePositiveEncode E<4*Nat.pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)+3 :=
      lt_of_le_of_lt (Nat.right_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)) (by omega)
    have hm : (4*Nat.pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)+3)%4=3 := by omega
    have hd : (4*Nat.pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)+3)/4=
        Nat.pair (rawNoteEncode rho.1) (multivariatePositiveEncode E) := by omega
    simpa only [multivariatePositiveEncode,encodedSingleCoreSupportStep,hm,hd,Nat.unpair_pair,
      show ¬(3=0) from by decide,show ¬(3=1) from by decide,show ¬(3=2) from by decide,if_false,singleCoreSupport]
      using ht E hE

private theorem table_source (n : Nat) : ∀ E : MultivariatePositiveExpr,multivariatePositiveEncode E<n →
    (encodedSingleCoreSupportTable n).getD (multivariatePositiveEncode E) []=singleCoreSupport E := by
  induction n with
  | zero => intro E he; omega
  | succ n ih =>
    intro E he
    by_cases heq : multivariatePositiveEncode E=n
    · rw [encodedSingleCoreSupportTable,List.getD_append_right _ _ _ _ (by rw [table_length]; omega)]
      simp only [table_length,heq,Nat.sub_self,List.getD_cons_zero]
      rw [←heq]
      apply step_source E
      intro F hF
      rw [heq]
      exact ih F (hF.trans_le (by omega))
    · rw [encodedSingleCoreSupportTable,List.getD_append _ _ _ _ (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem source (E : MultivariatePositiveExpr) :
    encodedSingleCoreSupport (multivariatePositiveEncode E)=singleCoreSupport E :=
  table_source _ E (Nat.lt_succ_self _)

theorem program : Targets.ActualSingleCoreSupportProgram := ⟨primitive,source⟩

end LogicLineages.OrdinalComparison.SingleCoreSupport
