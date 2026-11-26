module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations

theorem rename_index_primitive : Primrec (fun p : Nat × List Nat × Nat => renameIndex p.1 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : Nat × List Nat × Nat => p.1) := Primrec.fst
  have hr : Primrec (fun p : Nat × List Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : Nat × List Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.nat_lt.comp hi hk) hi
    (Primrec.nat_add.comp hk ((Primrec.list_getD 0).comp hr (Primrec.nat_sub.comp hi hk)))

theorem insert_index_primitive : Primrec₂ insertIndex :=
  Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst) Primrec.snd
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))

theorem rename_node_primitive : Primrec (fun p : List Nat × Node => renameNode p.1 p.2) := by
  have hr : Primrec (fun p : List Nat × Node => p.1) := Primrec.fst
  have ha : Primrec (fun p : List Nat × Node => p.2) := Primrec.snd
  have hd := Primrec.fst.comp ha
  have ht := Primrec.fst.comp (Primrec.snd.comp ha)
  have htag := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hargs := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hg := (Primrec.eq.comp htag (Primrec.const 0)).and
    (Primrec.eq.comp (Primrec.list_length.comp hargs) (Primrec.const 1))
  have hi := rename_index_primitive.comp ((Primrec.list_length.comp hd).pair
    (hr.pair ((Primrec.list_getD 0).comp hargs (Primrec.const 0))))
  have hb := hd.pair (ht.pair ((Primrec.const 0).pair (Primrec.list_cons.comp hi (Primrec.const []))))
  exact Primrec.ite hg hb ha

theorem insert_node_primitive : Primrec insertNode := by
  have hd : Primrec (fun a : Node => a.1) := Primrec.fst
  have ht : Primrec (fun a : Node => a.2.1) := Primrec.fst.comp Primrec.snd
  have htag : Primrec (fun a : Node => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hargs : Primrec (fun a : Node => a.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hg := (Primrec.eq.comp htag (Primrec.const 0)).and
    (Primrec.eq.comp (Primrec.list_length.comp hargs) (Primrec.const 1))
  have hi := insert_index_primitive.comp (Primrec.list_length.comp hd)
    ((Primrec.list_getD 0).comp hargs (Primrec.const 0))
  have hnew := Primrec.ite hg (Primrec.list_cons.comp hi (Primrec.const [])) hargs
  exact (Primrec.list_append.comp hd (Primrec.const [0])).pair (ht.pair (htag.pair hnew))

theorem append_table_primitive : Primrec (fun p : List Node × List Node => appendTable p.1 p.2) :=
  Primrec.list_append.comp Primrec.snd Primrec.fst

theorem rename_table_primitive : Primrec (fun p : List Nat × List Node => renameTable p.1 p.2) := by
  have hs : Primrec (fun p : (List Nat × List Node) × (Node × List Node) =>
      renameNode p.1.1 p.2.1 :: p.2.2) :=
    Primrec.list_cons.comp
      (rename_node_primitive.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr Primrec.snd (Primrec.const []) hs.to₂).of_eq
  intro p
  simp [renameTable,List.foldr_map,List.map_eq_foldr]

theorem insert_table_primitive : Primrec insertTable := by
  have hs : Primrec (fun p : List Node × (Node × List Node) => insertNode p.2.1 :: p.2.2) :=
    Primrec.list_cons.comp (insert_node_primitive.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr Primrec.id (Primrec.const []) hs.to₂).of_eq
  intro as
  simp [insertTable,List.foldr_map,List.map_eq_foldr]

theorem rename_code_primitive : Primrec (fun p : List Nat × List Nat × Code => renameCode p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : List Nat × List Nat × Code => p.1) := Primrec.fst
  have hr : Primrec (fun p : List Nat × List Nat × Code => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : List Nat × List Nat × Code => p.2.2) := Primrec.snd.comp Primrec.snd
  have hg := Primrec.fst.comp (Primrec.snd.comp hc)
  have hrest := Primrec.snd.comp (Primrec.snd.comp hc)
  exact ht.pair ((rename_table_primitive.comp (hr.pair hg)).pair hrest)

theorem primitive : RawSourceDAGOperationsTargets.Primitive :=
  ⟨append_table_primitive,rename_table_primitive,insert_table_primitive,rename_code_primitive⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
