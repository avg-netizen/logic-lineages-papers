module
public import LogicLineages.PermittedControl.OriginalUnitCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem unit_list_all_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun x => (f x).all (g x)) := by
  apply (Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro x
  induction f x with
  | nil => rfl
  | cons b bs ih => simp [List.foldr,ih]

 theorem originalLeadingCodeEffective : Primrec originalLeadingCode :=
  (Primrec.option_getD.comp (Primrec.list_head?.comp originalUnitCodesEffective) (Primrec.const 0)).of_eq (by
    intro n
    unfold originalLeadingCode
    cases originalUnitCodes n <;> rfl)

 theorem originalQuadraticRemainderEffective : Primrec originalQuadraticRemainder := by
  have hh := (Primrec.eq.comp Primrec.list_head? (Primrec.const (some (rawNoteEncode (ONote.ofNat 2))))).decide
  have ht : Primrec (fun l : List Nat => l.tail.all (fun e => decide (e=rawNoteEncode (ONote.ofNat 1)))) :=
    unit_list_all_primrec Primrec.list_tail (Primrec.eq.comp Primrec.snd (Primrec.const (rawNoteEncode (ONote.ofNat 1)))).decide.to₂
  exact Primrec.and.comp hh ht

 theorem initialPassCodeEffective : Primrec (fun p : Nat×Nat×Nat => initialPassCode p.1 p.2.1 p.2.2) := by
  have hm : Primrec (fun p : Nat×Nat×Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hl := originalUnitCodesEffective.comp hd
  have he := originalLeadingCodeEffective.comp hd
  have hc := rawProfileEffective.comp hm he
  have hc' := rawProfileEffective.comp hn he
  have heq := (Primrec.eq.comp hc hc').decide
  have hsmall : Primrec (fun p : Nat×Nat×Nat => (originalUnitCodes p.2.2).tail.all
      (fun e => decide (rawComparisonCode e (rawNoteEncode (ONote.ofNat 2))=0))) :=
    unit_list_all_primrec (Primrec.list_tail.comp hl)
      (Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp Primrec.snd (Primrec.const (rawNoteEncode (ONote.ofNat 2)))) (Primrec.const 0)).decide.to₂
  have hadj := ((Primrec.eq.comp hc (Primrec.nat_add.comp hc' (Primrec.const 1))).or
    (Primrec.eq.comp hc' (Primrec.nat_add.comp hc (Primrec.const 1)))).decide
  have hlarge := ((Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp (Primrec.const (rawNoteEncode (ONote.ofNat 3))) he) (Primrec.const 2)).not).decide
  have htwo := (Primrec.eq.comp he (Primrec.const (rawNoteEncode (ONote.ofNat 2)))).decide
  have hrem := originalQuadraticRemainderEffective.comp (Primrec.list_tail.comp hl)
  have hshape := Primrec.or.comp (Primrec.and.comp hlarge hrem) (Primrec.and.comp htwo hrem)
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp he
  have hpar := (Primrec.eq.comp (Primrec.nat_mod.comp
    (Primrec.nat_add.comp (Primrec.nat_min.comp hc hc') (Primrec.nat_add.comp (Primrec.const 1) hnorm))
    (Primrec.const 2)) (Primrec.const 1)).decide
  exact (Primrec.or.comp (Primrec.or.comp heq hsmall)
    (Primrec.and.comp (Primrec.and.comp hadj hshape) hpar)).of_eq (by intro p; rfl)

 theorem initialCodeEffective : Targets.InitialCodeEffective := ⟨originalUnitCodesEffective,initialPassCodeEffective⟩
end LogicLineages.PermittedControl
