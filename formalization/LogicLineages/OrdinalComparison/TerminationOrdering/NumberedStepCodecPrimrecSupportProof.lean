module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecSupportProof
open NumberedTypedFocus NumberedStepCertificate NumberedNumericStep NumberedStepCodecPrimrec

theorem positionTo : Primrec positionEquiv := Primrec.of_equiv
theorem positionFrom : Primrec positionEquiv.symm := Primrec.of_equiv_symm

theorem ordinaryPrimitive : Primrec Position.ordinaryBase :=
  (positionFrom.comp (Primrec.sumInr.comp ((Primrec.const (0 : Fin 3)).pair Primrec.id)))
theorem basePrimitive : Primrec Position.numberedBase :=
  (positionFrom.comp (Primrec.sumInr.comp ((Primrec.const (1 : Fin 3)).pair Primrec.id)))
theorem extrasPrimitive : Primrec Position.numberedExtras :=
  (positionFrom.comp (Primrec.sumInr.comp ((Primrec.const (2 : Fin 3)).pair Primrec.id)))

theorem positionEncoder : Primrec positionNumber := by
  have h : Primrec (fun p : Bool ⊕ (Fin 3 × Nat) =>
      p.elim (fun b => bif b then Nat.pair 1 0 else Nat.pair 0 0)
        (fun a => Nat.pair (a.1.val+2) a.2)) :=
    Primrec.sumCasesOn Primrec.id
      (Primrec.cond Primrec.snd (Primrec.const (Nat.pair 1 0)) (Primrec.const (Nat.pair 0 0))).to₂
      (Primrec₂.natPair.comp
        (Primrec.nat_add.comp (Primrec.fin_val.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 2))
        (Primrec.snd.comp Primrec.snd)).to₂
  exact (h.comp positionTo).of_eq (by intro p; cases p <;> rfl)

def decodePair (p : Nat × Nat) : Option Position :=
  if p.1=0 then if p.2=0 then some .lam else none
  else if p.1=1 then if p.2=0 then some .appFunction else none
  else if p.1=2 then some (.ordinaryBase p.2)
  else if p.1=3 then some (.numberedBase p.2)
  else if p.1=4 then some (.numberedExtras p.2) else none

theorem decodePairPrimitive : Primrec decodePair := by
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const (some Position.lam)) (Primrec.const none))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const (some Position.appFunction)) (Primrec.const none))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2))
        (Primrec.option_some.comp (ordinaryPrimitive.comp Primrec.snd))
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
          (Primrec.option_some.comp (basePrimitive.comp Primrec.snd))
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4))
            (Primrec.option_some.comp (extrasPrimitive.comp Primrec.snd)) (Primrec.const none)))))

theorem positionDecoder : Primrec decodePosition := by
  apply (decodePairPrimitive.comp Primrec.unpair).of_eq
  intro value
  unfold decodePair decodePosition
  generalize Nat.unpair value = p
  rcases p with ⟨tag,index⟩
  rcases tag with _ | _ | _ | _ | _ | tag <;> cases index <;> rfl

theorem positionsDecoder : Primrec decodePositions := by
  have hstep : Primrec₂ (fun (_ : List Nat) (p : Nat × Option (List Position)) =>
      (decodePosition p.1).bind (fun pos => p.2.map (pos::·))) := by
    change Primrec (fun p : List Nat × (Nat × Option (List Position)) =>
      (decodePosition p.2.1).bind (fun pos => p.2.2.map (pos::·)))
    apply Primrec.option_bind (positionDecoder.comp (Primrec.fst.comp Primrec.snd))
    apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const (some [])) hstep).of_eq
    (by intro xs; induction xs <;> simp_all [decodePositions, Option.map_eq_bind])

theorem certificateTo : Primrec certificateEquiv := Primrec.of_equiv
theorem certificateFrom : Primrec certificateEquiv.symm := Primrec.of_equiv_symm

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecSupportProof
