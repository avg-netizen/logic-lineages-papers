module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedHeadCodecPrimrec NumberedHeadCodecPrimrecSupportProof NumberedTypeCodecPrimrec NumberedTypeCodecPrimrecSupportProof

theorem arrowPrimitive : Primrec₂ Ty.arrow := by
  change Primrec (fun p : Ty × Ty => Ty.arrow p.1 p.2)
  apply (Primrec.of_equiv_iff typeEquiv).mp
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (typeTo.comp Primrec.fst) (typeTo.comp Primrec.snd))).of_eq
    (by intro p; simp [typeEquiv,NumberedLeastCodeRepresentative.typeNumber,Nat.add_comm])

theorem caseTypePrimitive : Primrec Ty.caseType :=
  arrowPrimitive.comp (Primrec.const Ty.ground)
    (arrowPrimitive.comp Primrec.id (arrowPrimitive.comp Primrec.id Primrec.id))

theorem recTypePrimitive : Primrec Ty.recType :=
  arrowPrimitive.comp (Primrec.const Ty.ground)
    (arrowPrimitive.comp
      (arrowPrimitive.comp (Primrec.const Ty.ground) (arrowPrimitive.comp Primrec.id Primrec.id))
      (arrowPrimitive.comp Primrec.id Primrec.id))

theorem headResultPrimitive : NumberedHeadSignaturePrimrecTargets.ActualHeadResultPrimitive := by
  intro n
  have h : Primrec (fun p : HeadData n => p.elim
      (fun b => bif b then Ty.arrow .ground .ground else .ground)
      (Sum.elim Ty.caseType (Sum.elim Ty.recType (Sum.elim Prod.snd (fun _ => Ty.ground))))) :=
    sumElim (Primrec.cond Primrec.id (Primrec.const (Ty.arrow .ground .ground)) (Primrec.const Ty.ground))
      (sumElim caseTypePrimitive (sumElim recTypePrimitive (sumElim Primrec.snd (Primrec.const Ty.ground))))
  exact (h.comp (headTo n)).of_eq (by intro head; cases head <;> rfl)

theorem headArgumentsPrimitive : NumberedHeadSignaturePrimrecTargets.ActualHeadArgumentsPrimitive := by
  intro n arity
  have harity : Primrec arity := Primrec.dom_finite arity
  have hground : Primrec (fun s : Fin n => List.replicate (arity s) Ty.ground) :=
    (Primrec.list_map (Primrec.list_range.comp harity) (Primrec₂.const Ty.ground)).of_eq
      (by intro s; simp)
  have happ : Primrec (fun p : Ty × Ty => [Ty.arrow p.1 p.2,p.1]) :=
    Primrec.list_cons.comp (arrowPrimitive.comp Primrec.fst Primrec.snd)
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
  have h : Primrec (fun p : HeadData n => p.elim (fun _ => ([] : List Ty))
      (Sum.elim (fun _ => []) (Sum.elim (fun _ => [])
        (Sum.elim (fun p => [Ty.arrow p.1 p.2,p.1]) (fun s => List.replicate (arity s) Ty.ground))))) :=
    sumElim (Primrec.const []) (sumElim (Primrec.const [])
      (sumElim (Primrec.const []) (sumElim happ hground)))
  exact (h.comp (headTo n)).of_eq (by intro head; cases head <;> rfl)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecProof
