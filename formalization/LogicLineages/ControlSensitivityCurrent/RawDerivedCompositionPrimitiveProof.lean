module
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionTargets
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
open LogicLineages.OrdinalComparison.Source
open Operations CheckedComposition

theorem detector_left_primitive : Primrec (fun p : Code × Code => detectorLeftRaw p.1 p.2) :=
  eraser_raw_primitive.comp
    ((eraser_raw_primitive.comp (Primrec.fst.pair Primrec.fst)).pair
     (eraser_raw_primitive.comp (Primrec.snd.pair Primrec.snd)))
theorem detector_right_primitive : Primrec (fun p : Code × Code => detectorRightRaw p.1 p.2) :=
  eraser_raw_primitive.comp
    ((eraser_raw_primitive.comp (Primrec.fst.pair Primrec.snd)).pair
     (eraser_raw_primitive.comp (Primrec.snd.pair Primrec.fst)))
theorem zero_primitive : Primrec zeroRaw :=
  Primrec.id.pair (Primrec.const ([rawNode 0 3 []],0,0))

theorem aggregate_raw_primitive : Primrec (fun p : List Nat × List (Code × Code) => aggregateRaw p.1 p.2) := by
  have hs : Primrec (fun p : (List Nat × List (Code × Code)) × ((Code × Code) × (Code × Code)) =>
      (eraserRaw (detectorLeftRaw p.2.1.1 p.2.1.2) p.2.2.1,
       eraserRaw (detectorRightRaw p.2.1.1 p.2.1.2) p.2.2.2)) := by
    have hp := Primrec.fst.comp (@Primrec.snd (List Nat × List (Code × Code)) ((Code × Code) × (Code × Code)) _ _)
    have ht := Primrec.snd.comp (@Primrec.snd (List Nat × List (Code × Code)) ((Code × Code) × (Code × Code)) _ _)
    exact (eraser_raw_primitive.comp ((detector_left_primitive.comp hp).pair (Primrec.fst.comp ht))).pair
      (eraser_raw_primitive.comp ((detector_right_primitive.comp hp).pair (Primrec.snd.comp ht)))
  apply (Primrec.list_foldr Primrec.snd
    ((zero_primitive.comp Primrec.fst).pair (zero_primitive.comp Primrec.fst)) hs.to₂).of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons a as ih => simp only [List.foldr_cons,aggregateRaw,ih]

theorem magnify_primitive : Primrec magnifyRaw := by
  have ht : Primrec (fun c : Code => c.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun c : Code => c.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha := Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_cons.comp hr (Primrec.const ([] : List Nat))))
  have hl := (Primrec.const ([] : List Nat)).pair
    ((Primrec.const (SyntaxCode.arrowCode 0 0)).pair ((Primrec.const 2).pair ha))
  have htable := Primrec.list_cons.comp (Primrec.const (rawNode 0 1 [0,1,0]))
    (Primrec.list_cons.comp (Primrec.const (rawNode 0 3 []))
      (Primrec.list_cons.comp hl (insert_table_primitive.comp ht)))
  exact Primrec.fst.pair (htable.pair (Primrec.const (0,0)))

theorem identity_primitive : Primrec identityRaw := by
  have ht : Primrec (fun c : Code => c.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun c : Code => c.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha := Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_cons.comp (Primrec.nat_add.comp (Primrec.const 2) hr) (Primrec.const ([] : List Nat))))
  have hn := (Primrec.const ([] : List Nat)).pair ((Primrec.const 0).pair ((Primrec.const 1).pair ha))
  have htable := Primrec.list_cons.comp hn
    (Primrec.list_cons.comp (Primrec.const (rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,0]))
      (Primrec.list_cons.comp (Primrec.const (([0],0,0,[0]) : Node)) ht))
  exact Primrec.fst.pair (htable.pair (Primrec.const (0,0)))

theorem constant_primitive : Primrec constantRaw := by
  have ht : Primrec (fun c : Code => c.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun c : Code => c.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha := Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_cons.comp (Primrec.nat_add.comp (Primrec.const 2) hr) (Primrec.const ([] : List Nat))))
  have hn := (Primrec.const ([] : List Nat)).pair ((Primrec.const 0).pair ((Primrec.const 1).pair ha))
  have htable := Primrec.list_cons.comp hn
    (Primrec.list_cons.comp (Primrec.const (rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,0]))
      (Primrec.list_cons.comp (Primrec.const (([0],0,3,[]) : Node)) ht))
  exact Primrec.fst.pair (htable.pair (Primrec.const (0,0)))

theorem wrapper_primitive : Primrec (fun p : Bool × Code => wrapperRaw p.1 p.2) := by
  apply (Primrec.cond Primrec.fst
    (constant_primitive.comp (magnify_primitive.comp Primrec.snd))
    (identity_primitive.comp (magnify_primitive.comp Primrec.snd))).of_eq
  intro p
  cases p.1 <;> rfl

/-- Internal extensional transfer from the actual primitive validator, not a new validation oracle. -/
theorem valid_primitive : Primrec valid :=
  RawValidator.check_primitive.of_eq RawValidator.check_eq_valid

theorem eraser_guard_primitive : Primrec (fun p : Code × Code => eraserGuard p.1 p.2) := by
  have ha : Primrec (fun p : Code × Code => p.1) := Primrec.fst
  have hb : Primrec (fun p : Code × Code => p.2) := Primrec.snd
  have hctx := (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)).decide
  have hat := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hbt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  exact Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp (valid_primitive.comp ha) (valid_primitive.comp hb)) hctx)
      (Primrec.eq.comp hat (Primrec.const 0)).decide)
    (Primrec.eq.comp hbt (Primrec.const 0)).decide

theorem aggregate_guard_primitive : Primrec (fun p : List Nat × List (Code × Code) => aggregateGuard p.1 p.2) := by
  have hs : Primrec (fun p : (List Nat × List (Code × Code)) × ((Code × Code) × Bool) =>
      eraserGuard p.2.1.1 p.2.1.2 && decide (p.2.1.1.1=p.1.1) && p.2.2) := by
    have hp := Primrec.fst.comp (@Primrec.snd (List Nat × List (Code × Code)) ((Code × Code) × Bool) _ _)
    have hc := Primrec.fst.comp (Primrec.fst.comp hp)
    have hΓ := Primrec.fst.comp (@Primrec.fst (List Nat × List (Code × Code)) ((Code × Code) × Bool) _ _)
    exact Primrec.and.comp
      (Primrec.and.comp (eraser_guard_primitive.comp hp) (Primrec.eq.comp hc hΓ).decide)
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) hs.to₂

theorem wrapper_guard_primitive : Primrec wrapperGuard :=
  Primrec.and.comp valid_primitive
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)).decide

theorem effective : RawDerivedCompositionTargets.Effective := by
  refine ⟨?_,?_,?_⟩
  · apply (Computable.cond eraser_guard_primitive.to_comp
      (Computable.option_some.comp (detector_left_primitive.pair detector_right_primitive).to_comp)
      (Computable.const none)).of_eq
    intro p
    cases h : eraserGuard p.1 p.2 <;> simp [detectors, h]
  · apply (Computable.cond aggregate_guard_primitive.to_comp
      (Computable.option_some.comp aggregate_raw_primitive.to_comp) (Computable.const none)).of_eq
    intro p
    cases h : aggregateGuard p.1 p.2 <;> simp [aggregate, h]
  · apply (Computable.cond (wrapper_guard_primitive.comp Primrec.snd).to_comp
      (Computable.option_some.comp wrapper_primitive.to_comp) (Computable.const none)).of_eq
    intro p
    cases h : wrapperGuard p.2 <;> simp [wrap, h]
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
