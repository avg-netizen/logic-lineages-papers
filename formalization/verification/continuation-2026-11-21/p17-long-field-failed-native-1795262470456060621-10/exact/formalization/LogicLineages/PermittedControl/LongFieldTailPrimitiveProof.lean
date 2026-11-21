module
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets
import LogicLineages.PermittedControl.ThresholdNumericProgramsProof
import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof
import LogicLineages.PermittedControl.EqualGapCertificateCodeProof
import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

theorem omegaMultipleTailCode_primrec : Primrec omegaMultipleTailCode := by
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (ordinalNodeCode_primrec (Primrec.const (rawNoteEncode (NONote.ofNat 1).1))
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) (Primrec.const 0))

private theorem longFieldPeelBoundCode_comp {α : Type*} [Primcodable α]
    {B lam mu c : α → Nat} (hB : Primrec B) (hl : Primrec lam) (hm : Primrec mu) (hc : Primrec c) :
    Primrec (fun p => longFieldPeelBoundCode (B p) (lam p) (mu p) (c p)) := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hp := hn.comp (ordinalAddCodeEffective.comp hm (omegaMultipleTailCode_primrec.comp hc))
  exact Primrec.nat_max.comp
    (Primrec.nat_max.comp (Primrec.const 2)
      (Primrec.nat_max.comp (hn.comp hl) (Primrec.nat_max.comp hp (hn.comp hm))))
    (Primrec.nat_max.comp (Primrec.nat_add.comp (hn.comp hm) (Primrec.const 3))
      (Primrec.nat_max.comp (Primrec.const 1) hB))

theorem longFieldPeelBoundCode_primrec :
    Primrec (fun p : Nat × Nat × Nat × Nat => longFieldPeelBoundCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  longFieldPeelBoundCode_comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem encodedLongGapTail_comp {α : Type*} [Primcodable α]
    {l m l' m' : α → Nat} (hl : Primrec l) (hm : Primrec m) (hl' : Primrec l') (hm' : Primrec m') :
    Primrec (fun p => encodedGapInputTail (l p,m p,l' p,m' p,0)) := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.const 2) (hn.comp hl)) (hn.comp hl'))
      (Primrec.nat_max.comp (Primrec.const 1) (Primrec.nat_max.comp (hn.comp hm) (hn.comp hm'))))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.const 0))

private abbrev TailArgs := Nat × LongFieldCode × LongFieldCode
private abbrev tailBudget (p : TailArgs) : Nat := p.1
private abbrev tailP (p : TailArgs) : LongFieldCode := p.2.1
private abbrev tailQ (p : TailArgs) : LongFieldCode := p.2.2

private theorem field_tag_code_primrec {G : TailArgs → LongFieldCode} (hG : Primrec G) :
    Primrec (fun p => (G p).1) := Primrec.fst.comp hG

private theorem field_exponent_code_primrec {G : TailArgs → LongFieldCode} (hG : Primrec G) :
    Primrec (fun p => (G p).2.1) := Primrec.fst.comp (Primrec.snd.comp hG)

private theorem field_upper_code_primrec {G : TailArgs → LongFieldCode} (hG : Primrec G) :
    Primrec (fun p => (G p).2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hG))

private theorem field_lower_code_primrec {G : TailArgs → LongFieldCode} (hG : Primrec G) :
    Primrec (fun p => (G p).2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hG))

private theorem tailP_primrec : Primrec tailP := Primrec.fst.comp Primrec.snd
private theorem tailQ_primrec : Primrec tailQ := Primrec.snd.comp Primrec.snd

theorem longFieldDistinctBoundCode_primrec :
    Primrec (fun p : Nat × LongFieldCode × LongFieldCode => longFieldDistinctBoundCode p.1 p.2.1 p.2.2) := by
  have hB : Primrec tailBudget := Primrec.fst
  have hP := Primrec.eq.comp (field_tag_code_primrec tailP_primrec) (Primrec.const 0)
  have hQ := Primrec.eq.comp (field_tag_code_primrec tailQ_primrec) (Primrec.const 0)
  have ha := field_exponent_code_primrec tailP_primrec
  have hb := field_exponent_code_primrec tailQ_primrec
  have hlp := field_upper_code_primrec tailP_primrec
  have hmp := field_lower_code_primrec tailP_primrec
  have hlq := field_upper_code_primrec tailQ_primrec
  have hmq := field_lower_code_primrec tailQ_primrec
  have hba := Primrec.nat_sub.comp hb ha
  have hab := Primrec.nat_sub.comp ha hb
  have hmp' := ordinalAddCodeEffective.comp hmp (omegaMultipleTailCode_primrec.comp hba)
  have hmq' := ordinalAddCodeEffective.comp hmq (omegaMultipleTailCode_primrec.comp hab)
  exact Primrec.ite hP (Primrec.ite hQ (Primrec.const 0) (longFieldPeelBoundCode_comp hB hlq hmq ha))
    (Primrec.ite hQ
      (Primrec.nat_max.comp (longFieldPeelBoundCode_comp hB hlp hmp (Primrec.const 0))
        (longFieldPeelBoundCode_comp hB hlp hmp hba))
      (Primrec.nat_max.comp
        (Primrec.nat_max.comp (longFieldPeelBoundCode_comp hB hlp hmp hba)
          (longFieldPeelBoundCode_comp hB hlq hmq hab))
        (Primrec.nat_max.comp
          (inverseTableTailCode_primrec hlp hmp' hmq' (ordinalSubCodeEffective.comp hlq hmq') hB)
          (encodedLongGapTail_comp hlq hmq' hlp hmp'))))

theorem longFieldSameBoundCode_primrec :
    Primrec (fun p : Nat × LongFieldCode × LongFieldCode => longFieldSameBoundCode p.1 p.2.1 p.2.2) := by
  have hB : Primrec tailBudget := Primrec.fst
  have hP := Primrec.eq.comp (field_tag_code_primrec tailP_primrec) (Primrec.const 0)
  have hQ := Primrec.eq.comp (field_tag_code_primrec tailQ_primrec) (Primrec.const 0)
  have ha := field_exponent_code_primrec tailP_primrec
  have hb := field_exponent_code_primrec tailQ_primrec
  have hlp := field_upper_code_primrec tailP_primrec
  have hmp := field_lower_code_primrec tailP_primrec
  have hlq := field_upper_code_primrec tailQ_primrec
  have hmq := field_lower_code_primrec tailQ_primrec
  have hba := Primrec.nat_sub.comp hb ha
  have hab := Primrec.nat_sub.comp ha hb
  have hmp' := ordinalAddCodeEffective.comp hmp (omegaMultipleTailCode_primrec.comp hba)
  have hmq' := ordinalAddCodeEffective.comp hmq (omegaMultipleTailCode_primrec.comp hab)
  have hcert := equalGapCertificateTailEffective.comp
    (hmp'.pair (hmq'.pair ((ordinalSubCodeEffective.comp hlp hmp').pair hB)))
  exact Primrec.ite hP
    (Primrec.ite hQ (Primrec.const 0) (longFieldPeelBoundCode_comp hB hlq hmq (Primrec.succ.comp ha)))
    (Primrec.ite hQ (longFieldPeelBoundCode_comp hB hlp hmp (Primrec.succ.comp hb))
      (Primrec.nat_max.comp
        (Primrec.nat_max.comp (longFieldPeelBoundCode_comp hB hlp hmp hba)
          (longFieldPeelBoundCode_comp hB hlq hmq hab))
        (Primrec.nat_max.comp
          (Primrec.nat_max.comp (encodedLongGapTail_comp hlq hmq' hlp hmp')
            (encodedLongGapTail_comp hlp hmp' hlq hmq')) hcert)))

end LogicLineages.PermittedControl.FieldComparison
