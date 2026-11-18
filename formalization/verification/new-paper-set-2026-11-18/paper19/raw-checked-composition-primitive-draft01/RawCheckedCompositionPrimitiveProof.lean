module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGEffectiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
open LogicLineages.OrdinalComparison.Source
open Operations

theorem application_raw_primitive : Primrec (fun p : Nat × Code × Code => applicationRaw p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Nat × Code × Code => p.1) := Primrec.fst
  have hf : Primrec (fun p : Nat × Code × Code => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × Code × Code => p.2.2) := Primrec.snd.comp Primrec.snd
  have hΓ := Primrec.fst.comp hf
  have hft := Primrec.fst.comp (Primrec.snd.comp hf)
  have hat := Primrec.fst.comp (Primrec.snd.comp ha)
  have hfr := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hf))
  have har := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have haσ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hargs := Primrec.list_cons.comp haσ (Primrec.list_cons.comp
    (Primrec.nat_add.comp (Primrec.list_length.comp hat) hfr)
    (Primrec.list_cons.comp har (Primrec.const [])))
  have hn := (Primrec.const []).pair (ht.pair ((Primrec.const 1).pair hargs))
  have htable := Primrec.list_cons.comp hn (append_table_primitive.comp (hft.pair hat))
  exact hΓ.pair (htable.pair ((Primrec.const 0).pair ht))

theorem eraser_raw_primitive : Primrec (fun p : Code × Code => eraserRaw p.1 p.2) := by
  have ha : Primrec (fun p : Code × Code => p.1) := Primrec.fst
  have hb : Primrec (fun p : Code × Code => p.2) := Primrec.snd
  have hΓ := Primrec.fst.comp ha
  have hat := Primrec.fst.comp (Primrec.snd.comp ha)
  have hbt := Primrec.fst.comp (Primrec.snd.comp hb)
  have har := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hbr := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have happArgs := Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_cons.comp (Primrec.nat_add.comp (Primrec.const 1) hbr) (Primrec.const [])))
  have hlamArgs := Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_cons.comp (Primrec.nat_add.comp (Primrec.list_length.comp hbt) har) (Primrec.const [])))
  have happ := (Primrec.const []).pair ((Primrec.const 0).pair ((Primrec.const 1).pair happArgs))
  have hlam := (Primrec.const []).pair ((Primrec.const (SyntaxCode.arrowCode 0 0)).pair ((Primrec.const 2).pair hlamArgs))
  have htable := Primrec.list_cons.comp happ (Primrec.list_cons.comp hlam
    (append_table_primitive.comp ((insert_table_primitive.comp hat).pair hbt)))
  exact hΓ.pair (htable.pair (Primrec.const (0,0)))

theorem application_guard_computable : Computable (fun p : Nat × Code × Code => applicationGuard p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Nat × Code × Code => p.1) := Primrec.fst
  have hf : Primrec (fun p : Nat × Code × Code => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : Nat × Code × Code => p.2.2) := Primrec.snd.comp Primrec.snd
  have hctx := (Primrec.eq.comp (Primrec.fst.comp hf) (Primrec.fst.comp ha)).decide.to_comp
  have hft := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hf))
  have hat := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have harrow := Primrec.nat_add.comp (Primrec₂.natPair.comp hat ht) (Primrec.const 1)
  have hty := (Primrec.eq.comp hft harrow).decide.to_comp
  exact Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp
      (Primrec.and.to_comp.comp (valid_computable.comp hf.to_comp) (valid_computable.comp ha.to_comp)) hctx) hty

theorem eraser_guard_computable : Computable (fun p : Code × Code => eraserGuard p.1 p.2) := by
  have ha : Primrec (fun p : Code × Code => p.1) := Primrec.fst
  have hb : Primrec (fun p : Code × Code => p.2) := Primrec.snd
  have hctx := (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)).decide.to_comp
  have hat := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hbt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  exact Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp
      (Primrec.and.to_comp.comp
        (Primrec.and.to_comp.comp (valid_computable.comp ha.to_comp) (valid_computable.comp hb.to_comp)) hctx)
      (Primrec.eq.comp hat (Primrec.const 0)).decide.to_comp)
    (Primrec.eq.comp hbt (Primrec.const 0)).decide.to_comp

theorem effective : RawCheckedCompositionTargets.Effective := by
  constructor
  · apply (Computable.cond application_guard_computable
      (Computable.option_some.comp application_raw_primitive.to_comp) (Computable.const none)).of_eq
    intro p
    unfold application
    cases applicationGuard p.1 p.2.1 p.2.2 <;> rfl
  · apply (Computable.cond eraser_guard_computable
      (Computable.option_some.comp eraser_raw_primitive.to_comp) (Computable.const none)).of_eq
    intro p
    unfold eraser
    cases eraserGuard p.1 p.2 <;> rfl
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
