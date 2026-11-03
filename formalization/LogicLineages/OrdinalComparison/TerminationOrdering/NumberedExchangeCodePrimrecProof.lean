module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodePrimrecProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedExchangeCode NumberedExchangeCodeFieldsProof
open NumberedSyntaxBoundsPrimrecSupportProof NumberedHeadSignaturePrimrecProof

abbrev LayerInput (n : Nat) :=
  (List (Fin n) × List Ty) × Fields n × Fields n × List Bool

/-- The literal checker with its recursive calls replaced by aligned child answers. -/
def layer (n : Nat) (arity : Fin n → Nat) (p : LayerInput n) : Bool :=
  let x := p.2.1
  let y := p.2.2.1
  let left := p.2.2.2.getD 0 false
  let right := p.2.2.2.getD 3 false
  let root := headMove arity p.1.1 p.1.2 x.2.2.1 x.2.2.2.2.2.1
    y.2.2.1 y.2.2.2.2.2.1
  if x.1 = y.1 then
    if x.1 = 1 then decide (x.2.1 = y.2.1) && left
    else if x.1 = 2 then decide (x.2.1 = y.2.1) &&
      ((decide (x.2.2.2.2.2.2 = y.2.2.2.2.2.2) && left) ||
        (decide (x.2.2.2.2.2.1 = y.2.2.2.2.2.1) && right))
    else if x.1 = 4 then
      (root && decide (headResult (decodeHead y.2.2.1) = headResult (decodeHead x.2.2.1))) ||
        (decide (x.2.2.1 = y.2.2.1) && left)
    else if x.1 = 5 then
      decide (x.2.2.2.1 = y.2.2.2.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.2.2.1 = y.2.2.2.2.1) &&
        ((decide (x.2.2.2.2.2.2 = y.2.2.2.2.2.2) && root) ||
          (decide (x.2.2.1 = y.2.2.1 ∧ x.2.2.2.2.2.2 = y.2.2.2.2.2.2) && left) ||
          (decide (x.2.2.1 = y.2.2.1 ∧ x.2.2.2.2.2.1 = y.2.2.2.2.2.1) && right))
    else if x.1 = 7 then decide (x.2.1 = y.2.1) &&
      ((decide (x.2.2.2.2.2.2 = y.2.2.2.2.2.2) && left) ||
        (decide (x.2.2.2.2.2.1 = y.2.2.2.2.2.1) && right))
    else false
  else false

theorem layerPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (layer n arity) := by
  have hwindow : Primrec (fun p : LayerInput n => (p.1 : List (Fin n) × List Ty)) := (Primrec.fst.comp Primrec.id)
  have hanswers : Primrec (fun p : LayerInput n => (p.2.2.2 : List Bool)) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
  have hxtag : Primrec (fun p : LayerInput n => (p.2.1.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
  have hxann : Primrec (fun p : LayerInput n => (p.2.1.2.1 : Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))
  have hxhead : Primrec (fun p : LayerInput n => (p.2.1.2.2.1 : HeadCode (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))))
  have hxlabel : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))))
  have hxtypes : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.2.1 : List Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))))))
  have hxfirst : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.2.2.1 : Code (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))))))
  have hxsecond : Primrec (fun p : LayerInput n => (p.2.1.2.2.2.2.2.2 : Code (Fin n))) :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))))))
  have hytag : Primrec (fun p : LayerInput n => (p.2.2.1.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  have hyann : Primrec (fun p : LayerInput n => (p.2.2.1.2.1 : Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))
  have hyhead : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.1 : HeadCode (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))
  have hylabel : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.1 : Nat)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))
  have hytypes : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.2.1 : List Ty)) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))))
  have hyfirst : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.2.2.1 : Code (Fin n))) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))))
  have hysecond : Primrec (fun p : LayerInput n => (p.2.2.1.2.2.2.2.2.2 : Code (Fin n))) :=
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))))))

  have hleft : Primrec (fun p : LayerInput n => p.2.2.2.getD 0 false) :=
    (Primrec.list_getD false).comp hanswers (Primrec.const 0)
  have hright : Primrec (fun p : LayerInput n => p.2.2.2.getD 3 false) :=
    (Primrec.list_getD false).comp hanswers (Primrec.const 3)
  have hroot : Primrec (fun p : LayerInput n =>
      headMove arity p.1.1 p.1.2 p.2.1.2.2.1 p.2.1.2.2.2.2.2.1
        p.2.2.1.2.2.1 p.2.2.1.2.2.2.2.2.1) :=
    (NumberedExchangeRootPrimrecProof.headMovePrimitive n arity).comp
      (hwindow.pair ((hxhead.pair hxfirst).pair (hyhead.pair hyfirst)))
  have hann := (Primrec.eq.comp hxann hyann).decide
  have hfirst := (Primrec.eq.comp hxfirst hyfirst).decide
  have hsecond := (Primrec.eq.comp hxsecond hysecond).decide
  have hhead := (Primrec.eq.comp hxhead hyhead).decide
  have hresult := (Primrec.eq.comp ((headResultPrimitive n).comp hyhead)
    ((headResultPrimitive n).comp hxhead)).decide
  have hannotations := ((Primrec.eq.comp hxlabel hylabel).and
    ((Primrec.eq.comp hxann hyann).and (Primrec.eq.comp hxtypes hytypes))).decide
  have hheadSecond := ((Primrec.eq.comp hxhead hyhead).and
    (Primrec.eq.comp hxsecond hysecond)).decide
  have hheadFirst := ((Primrec.eq.comp hxhead hyhead).and
    (Primrec.eq.comp hxfirst hyfirst)).decide
  have hlam := Primrec.and.comp hann hleft
  have happ := Primrec.and.comp hann
    (Primrec.or.comp (Primrec.and.comp hsecond hleft) (Primrec.and.comp hfirst hright))
  have hordinary := Primrec.or.comp (Primrec.and.comp hroot hresult)
    (Primrec.and.comp hhead hleft)
  have hnumbered := Primrec.and.comp hannotations
    (Primrec.or.comp
      (Primrec.or.comp (Primrec.and.comp hsecond hroot) (Primrec.and.comp hheadSecond hleft))
      (Primrec.and.comp hheadFirst hright))
  exact Primrec.ite (Primrec.eq.comp hxtag hytag)
    (Primrec.ite (Primrec.eq.comp hxtag (Primrec.const 1)) hlam
      (Primrec.ite (Primrec.eq.comp hxtag (Primrec.const 2)) happ
        (Primrec.ite (Primrec.eq.comp hxtag (Primrec.const 4)) hordinary
          (Primrec.ite (Primrec.eq.comp hxtag (Primrec.const 5)) hnumbered
            (Primrec.ite (Primrec.eq.comp hxtag (Primrec.const 7)) happ (Primrec.const false))))))
    (Primrec.const false)

theorem layerCalibration (n : Nat) (arity : Fin n → Nat)
    (window : List (Fin n) × List Ty) (source target : Code (Fin n)) :
    layer n arity (window, fields source, fields target,
      (dependencies (source, target)).map
        (fun p => codeExchange arity window.1 window.2 p.1 p.2)) =
      codeExchange arity window.1 window.2 source target := by
  cases source <;> cases target <;>
    simp [layer, fields, dependencies, NumberedCodeEnumerationPrimrecSupportProof.cross,
      children, codeExchange, List.getD] <;> rfl

theorem codeExchangePrimitive : NumberedExchangePrimrecTargets.ActualCodeExchangePrimitive := by
  intro n arity
  change Primrec₂ (fun (window : List (Fin n) × List Ty) (p : Code (Fin n) × Code (Fin n)) =>
    codeExchange arity window.1 window.2 p.1 p.2)
  apply Primrec.nat_omega_rec
    (m := fun (_ : List (Fin n) × List Ty) (p : Code (Fin n) × Code (Fin n)) => codeNumber p.1)
    (l := fun (_ : List (Fin n) × List Ty) p => dependencies p)
    (g := fun window p => some (layer n arity
      (window, fields p.1.1, fields p.1.2, p.2)))
  · exact ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp
      (Primrec.fst.comp Primrec.snd)).to₂
  · exact ((dependenciesPrimitive n).comp Primrec.snd).to₂
  · exact (Primrec.option_some.comp ((layerPrimitive n arity).comp
      (Primrec.fst.pair
        (((fieldsPrimitive n).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair
          (((fieldsPrimitive n).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))).pair
            (Primrec.snd.comp Primrec.snd)))))).to₂
  · intro window p child hchild
    exact dependenciesDecrease n p child hchild
  · intro window p
    exact congrArg some (layerCalibration n arity window p.1 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodePrimrecProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodePrimrecProof
