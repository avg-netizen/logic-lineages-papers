module
public import LogicLineages.OrdinalComparison.SingleCoreBoxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

theorem words_primitive : Primrec₂ singleCoreBoxWords := by
  let A := Nat × (Nat × List (List Nat))
  have hPrev : Primrec (fun p : A × Nat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hMap : Primrec₂ (fun p : A => fun value : Nat => p.2.2.map (fun word => (value+1)::word)) :=
    Primrec.list_map hPrev (Primrec.list_cons.comp
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hRange : Primrec (fun p : A => List.range (p.1-1)) :=
    Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
  have hStep : Primrec₂ (fun bound : Nat => fun state : Nat × List (List Nat) =>
      (List.range (bound-1)).flatMap (fun value => state.2.map (fun word => (value+1)::word))) :=
    Primrec.list_flatMap hRange hMap
  apply (Primrec.nat_rec (Primrec.const ([[]] : List (List Nat))) hStep).of_eq
  intro bound n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (List.range (bound-1)).flatMap (fun value =>
      (Nat.rec (motive := fun _ => List (List Nat)) [[]] (fun _ previous => (List.range (bound-1)).flatMap
        (fun value => previous.map (fun word => (value+1)::word))) n).map (fun word => (value+1)::word))=_
    rw [ih]
    rfl

theorem lookup_primitive : Primrec (fun p : List Nat × List Nat × Nat => singleCoreBoxLookup p.1 p.2.1 p.2.2) := by
  have hFind : Primrec (fun p : List Nat × List Nat × Nat => p.1.findIdx (fun j => decide (j=p.2.2))) :=
    Primrec.list_findIdx Primrec.fst
      (Primrec.eq.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).decide
  exact (Primrec.list_getD 1).comp (Primrec.fst.comp Primrec.snd) hFind

theorem tuple_primitive : Primrec (fun p : Nat × List Nat × List Nat => singleCoreBoxTuple p.1 p.2.1 p.2.2) := by
  have hSupport : Primrec (fun p : (Nat × List Nat × List Nat) × Nat => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hWord : Primrec (fun p : (Nat × List Nat × List Nat) × Nat => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hLookup := lookup_primitive.comp (hSupport.pair (hWord.pair Primrec.snd))
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    (Primrec.nat_sub.comp hLookup (Primrec.const 1))

theorem point_program : Computable₂ encodedSingleCoreRowPoint := by
  have hParts := SingleCoreRowCompiler.parts_primitive.comp (Primrec.fst : Primrec (fun p : EncodedSingleCoreRow × Nat => p.1))
  have hLeft := encodedPositiveEvaluationComputable.comp (Primrec.fst.comp hParts).to_comp Computable.snd
  have hRight := encodedPositiveEvaluationComputable.comp (Primrec.snd.comp hParts).to_comp Computable.snd
  exact ComparisonNode.point_program.1.to_comp.comp hLeft hRight

theorem box_program : Computable (fun p : Nat × EncodedSingleCoreRow × List Nat => encodedSingleCoreBoxSign p.1 p.2.1 p.2.2) := by
  have hSource : Primrec (fun p : Nat × EncodedSingleCoreRow × List Nat => p.1) := Primrec.fst
  have hRow : Primrec (fun p : Nat × EncodedSingleCoreRow × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hWord : Primrec (fun p : Nat × EncodedSingleCoreRow × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hTuple := tuple_primitive.comp (hSource.pair ((SingleCoreSupport.primitive.comp hSource).pair hWord))
  have hValue := SingleCoreEvaluation.program.comp hSource.to_comp hTuple.to_comp
  exact point_program.comp hRow.to_comp hValue

end LogicLineages.OrdinalComparison.SingleCorePresburger
