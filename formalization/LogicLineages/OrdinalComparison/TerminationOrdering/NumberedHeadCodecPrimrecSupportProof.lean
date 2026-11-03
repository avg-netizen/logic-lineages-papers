module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecSupportProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedTypeCodecPrimrec NumberedHeadCodecPrimrec

theorem headTo (n : Nat) : Primrec (headEquiv n) := Primrec.of_equiv
theorem headFrom (n : Nat) : Primrec (headEquiv n).symm := Primrec.of_equiv_symm

theorem casesPrimitive (n : Nat) : Primrec (@HeadCode.cases (Fin n)) :=
  (headFrom n).comp (Primrec.sumInr.comp Primrec.sumInl)
theorem recursorPrimitive (n : Nat) : Primrec (@HeadCode.recursor (Fin n)) :=
  (headFrom n).comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))
theorem applicationPrimitive (n : Nat) : Primrec (fun p : Ty × Ty => (HeadCode.application p.1 p.2 : HeadCode (Fin n))) :=
  (headFrom n).comp (Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl)))
theorem rankedPrimitive (n : Nat) : Primrec (@HeadCode.ranked (Fin n)) :=
  (headFrom n).comp (Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr)))

theorem sumElim {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {f : A → C} {g : B → C} (hf : Primrec f) (hg : Primrec g) : Primrec (Sum.elim f g) :=
  Primrec.sumCasesOn Primrec.id (hf.comp Primrec.snd).to₂ (hg.comp Primrec.snd).to₂

theorem encoder (n : Nat) : Primrec (@headNumber n) := by
  have h : Primrec (fun p : HeadData n => p.elim
      (fun b => bif b then Nat.pair 1 0 else Nat.pair 0 0)
      (Sum.elim (fun tau => Nat.pair 2 (typeNumber tau))
        (Sum.elim (fun tau => Nat.pair 3 (typeNumber tau))
          (Sum.elim (fun p => Nat.pair 4 (Nat.pair (typeNumber p.1) (typeNumber p.2)))
            (fun s => Nat.pair 5 s.val))))) :=
    sumElim (Primrec.cond Primrec.id (Primrec.const (Nat.pair 1 0)) (Primrec.const (Nat.pair 0 0)))
      (sumElim (Primrec₂.natPair.comp (Primrec.const 2) NumberedTypeCodecPrimrecProof.typeEncoderPrimitive)
        (sumElim (Primrec₂.natPair.comp (Primrec.const 3) NumberedTypeCodecPrimrecProof.typeEncoderPrimitive)
          (sumElim (Primrec₂.natPair.comp (Primrec.const 4)
            (Primrec₂.natPair.comp (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.fst)
              (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.snd)))
            (Primrec₂.natPair.comp (Primrec.const 5) Primrec.fin_val))))
  exact (h.comp (headTo n)).of_eq (by intro head; cases head <;> rfl)

theorem finDecode (n value : Nat) : (Encodable.decode value : Option (Fin n)) =
    if h : value<n then some ⟨value,h⟩ else none := by
  with_reducible_and_instances change @Encodable.decode (Fin n) (Fin.encodable n) value = _
  simp only [Fin.encodable,Encodable.decode_ofEquiv]
  with_reducible_and_instances change ((Encodable.decodeSubtype value : Option {v : Nat // v<n}).map Fin.equivSubtype.symm)=_
  simp only [Encodable.decodeSubtype,Encodable.decode_nat,Option.bind_some]
  split <;> rfl

def pairParse (n : Nat) (p : Nat × Nat) : Option (HeadCode (Fin n)) :=
  if p.1=0 then if p.2=0 then some .zero else none
  else if p.1=1 then if p.2=0 then some .succ else none
  else if p.1=2 then (decodeType p.2).map HeadCode.cases
  else if p.1=3 then (decodeType p.2).map HeadCode.recursor
  else if p.1=4 then do
    let sigma ← decodeType (Nat.unpair p.2).1
    let tau ← decodeType (Nat.unpair p.2).2
    pure (.application sigma tau)
  else if p.1=5 then (Encodable.decode p.2 : Option (Fin n)).map HeadCode.ranked
  else none

theorem pairParserPrimitive (n : Nat) : Primrec (pairParse n) := by
  have happ : Primrec (fun p : Nat × Nat => do
      let sigma ← decodeType (Nat.unpair p.2).1
      let tau ← decodeType (Nat.unpair p.2).2
      pure (HeadCode.application sigma tau : HeadCode (Fin n))) := by
    apply Primrec.option_bind (NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    have h : Primrec (fun p : (Nat × Nat) × Ty =>
        (decodeType (Nat.unpair p.1.2).2).map (fun tau => (HeadCode.application p.2 tau : HeadCode (Fin n)))) := Primrec.option_map (NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
      ((applicationPrimitive n).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂
    exact h.to₂.of_eq (by intro p sigma; simp [Option.map_eq_bind])
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (Primrec.const (some (HeadCode.zero : HeadCode (Fin n)))) (Primrec.const none))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Primrec.const (some (HeadCode.succ : HeadCode (Fin n)))) (Primrec.const none))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2))
        (Primrec.option_map (NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp Primrec.snd)
          ((casesPrimitive n).comp Primrec.snd).to₂)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
          (Primrec.option_map (NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp Primrec.snd)
            ((recursorPrimitive n).comp Primrec.snd).to₂)
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4)) happ
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
              (Primrec.option_map (Primrec.decode.comp Primrec.snd) ((rankedPrimitive n).comp Primrec.snd).to₂)
              (Primrec.const none))))))

theorem parser (n : Nat) : Primrec (headParse n) := by
  apply ((pairParserPrimitive n).comp Primrec.unpair).of_eq
  intro value
  unfold pairParse headParse
  generalize Nat.unpair value=p
  rcases p with ⟨tag,payload⟩
  rcases tag with _ | _ | _ | _ | _ | _ | tag
  · cases payload <;> rfl
  · cases payload <;> rfl
  · rfl
  · rfl
  · rfl
  · simp [finDecode]
  · rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecSupportProof
