module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableEffectivityProof
open NumberedNumericDecoding NumberedCodeParserTable

theorem lookupPrimitive : Primrec₂ lookup := Primrec.list_getD false

theorem nextPrimitive (n : Nat) : Primrec₂ (codeNext n) := by
  have h : Primrec (fun p : List Bool × Nat =>
      if (Nat.unpair p.2).1=0 then true else
      if (Nat.unpair p.2).1=1 then ((decodeType ((Nat.unpair (Nat.unpair p.2).2).1)).isSome && lookup p.1 ((Nat.unpair (Nat.unpair p.2).2).2)) else
      if (Nat.unpair p.2).1=2 then (((decodeType ((Nat.unpair (Nat.unpair p.2).2).1)).isSome && lookup p.1 ((Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).1)) && lookup p.1 ((Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2)) else
      if (Nat.unpair p.2).1=3 then (decodeType ((Nat.unpair p.2).2)).isSome else
      if (Nat.unpair p.2).1=4 then ((decodeHeadNumber n ((Nat.unpair (Nat.unpair p.2).2).1)).isSome && lookup p.1 ((Nat.unpair (Nat.unpair p.2).2).2)) else
      if (Nat.unpair p.2).1=5 then (((((decodeHeadNumber n ((Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).1)).isSome && (decodeType ((Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2).1)).isSome) && lookup p.1 ((Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2).2).1)) && (decodeTypes ((Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2).2).2).1)).isSome) && lookup p.1 ((Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2).2).2).2)) else
      if (Nat.unpair p.2).1=6 then (decide ((Nat.unpair p.2).2=0)) else
      if (Nat.unpair p.2).1=7 then (((decodeType ((Nat.unpair (Nat.unpair p.2).2).1)).isSome && lookup p.1 ((Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).1)) && lookup p.1 ((Nat.unpair (Nat.unpair (Nat.unpair p.2).2).2).2)) else
      false) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 0)) (Primrec.const true) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 1)) (Primrec.and.comp (Primrec.option_isSome.comp ((NumberedTypeCodecPrimrecProof.typeDecoderPrimitive).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))) (lookupPrimitive.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 2)) (Primrec.and.comp (Primrec.and.comp (Primrec.option_isSome.comp ((NumberedTypeCodecPrimrecProof.typeDecoderPrimitive).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))) (lookupPrimitive.comp Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))) (lookupPrimitive.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 3)) (Primrec.option_isSome.comp ((NumberedTypeCodecPrimrecProof.typeDecoderPrimitive).comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 4)) (Primrec.and.comp (Primrec.option_isSome.comp ((NumberedHeadCodecPrimrecProof.headDecoderPrimitive n).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))) (lookupPrimitive.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 5)) (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.option_isSome.comp ((NumberedHeadCodecPrimrecProof.headDecoderPrimitive n).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))) (Primrec.option_isSome.comp ((NumberedTypeCodecPrimrecProof.typeDecoderPrimitive).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))))))) (lookupPrimitive.comp Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))))))) (Primrec.option_isSome.comp ((NumberedTypeCodecPrimrecProof.typeListDecoderPrimitive).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))))))))))))) (lookupPrimitive.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))))))))) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 6)) (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 0)).decide (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const 7)) (Primrec.and.comp (Primrec.and.comp (Primrec.option_isSome.comp ((NumberedTypeCodecPrimrecProof.typeDecoderPrimitive).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))) (lookupPrimitive.comp Primrec.fst (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))) (lookupPrimitive.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))))) ((Primrec.const false)))))))))
  apply h.of_eq
  intro p
  rcases p with ⟨previous,value⟩
  unfold codeNext
  generalize ht : (Nat.unpair value).1=tag
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag <;> rfl

theorem tablePrimitive (n : Nat) : Primrec₂ (codeTable n) := by
  have hzero : Primrec (fun bound : Nat => List.replicate (bound+1) false) :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.succ) (Primrec₂.const false)).of_eq (by intro bound; simp)
  have hstep : Primrec₂ (fun bound (state : Nat × List Bool) =>
      (List.range (bound+1)).map (codeNext n state.2)) := by
    change Primrec (fun p : Nat × (Nat × List Bool) =>
      (List.range (p.1+1)).map (codeNext n p.2.2))
    exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
      ((nextPrimitive n).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  exact (Primrec.nat_rec hzero hstep).of_eq (by intro bound fuel; induction fuel <;> simp_all [codeTable])

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableEffectivityProof
