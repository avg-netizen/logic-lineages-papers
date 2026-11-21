module
public import LogicLineages.PermittedControl.RawFieldComparisonFormTargets
import LogicLineages.PermittedControl.LongFieldTailPrimitiveProof
import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof
import LogicLineages.PermittedControl.PureCertificateCodeProof
import LogicLineages.PermittedControl.EqualGapCertificateCodeProof
import LogicLineages.OrdinalComparison.RawComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private abbrev FormArgs := LongFieldCode × LongFieldCode

private theorem pCode : Primrec (fun p : FormArgs => p.1) := Primrec.fst
private theorem qCode : Primrec (fun p : FormArgs => p.2) := Primrec.snd

private theorem isIterate {F : FormArgs → LongFieldCode} (hF : Primrec F) :
    PrimrecPred (fun p => (F p).1 = 0) :=
  Primrec.eq.comp (Primrec.fst.comp hF) (Primrec.const 0)

private theorem exponentCode {F : FormArgs → LongFieldCode} (hF : Primrec F) :
    Primrec (fun p => (F p).2.1) := Primrec.fst.comp (Primrec.snd.comp hF)

private theorem upperCode {F : FormArgs → LongFieldCode} (hF : Primrec F) :
    Primrec (fun p => (F p).2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hF))

private theorem lowerCode {F : FormArgs → LongFieldCode} (hF : Primrec F) :
    Primrec (fun p => (F p).2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hF))

private theorem linearFormComp {S tag a l m : FormArgs → Nat} (hs : Primrec S) (ht : Primrec tag)
    (ha : Primrec a) (hl : Primrec l) (hm : Primrec m) :
    Primrec (fun p => rawLinearForm (S p) (tag p,a p,l p,m p)) :=
  (Primrec.const 1).pair (hs.pair (ht.pair (ha.pair (hl.pair hm))))

private theorem rawDistinctForm_primrec : Primrec₂ rawDistinctForm := by
  have hP := isIterate pCode
  have hQ := isIterate qCode
  have ha := exponentCode pCode
  have hb := exponentCode qCode
  have hlp := upperCode pCode
  have hmp := lowerCode pCode
  have hlq := upperCode qCode
  have hmq := lowerCode qCode
  have hba := Primrec.nat_sub.comp hb ha
  have hab := Primrec.nat_sub.comp ha hb
  have hmp' := ordinalAddCodeEffective.comp hmp (omegaMultipleTailCode_primrec.comp hba)
  have hmq' := ordinalAddCodeEffective.comp hmq (omegaMultipleTailCode_primrec.comp hab)
  have hdp := ordinalSubCodeEffective.comp hlp hmp'
  have hdq := ordinalSubCodeEffective.comp hlq hmq'
  have hcmp := rawComparisonPrimitiveRecursive.comp hdq hdp
  have hsign := equalGapCertificateSignEffective.comp (hmp'.pair (hmq'.pair hdq))
  have hH := ordinalAddCodeEffective.comp hmp' hdq
  have hconst : Primrec (fun _ : FormArgs => rawConstForm 0) := Primrec.const _
  have hzero : Primrec (fun _ : FormArgs => (0 : Nat)) := Primrec.const 0
  have hone : Primrec (fun _ : FormArgs => (1 : Nat)) := Primrec.const 1
  exact Primrec.ite hP
    (Primrec.ite hQ
      (Primrec.ite (Primrec.nat_le.comp ha hb) hconst
        (linearFormComp hone hzero hab hzero hzero))
      hconst)
    (Primrec.ite hQ
      (Primrec.ite (Primrec.nat_le.comp hb ha)
        (linearFormComp hone hone hab hlp hmp)
        (linearFormComp hone hone hzero hlp hmp'))
      (Primrec.ite (Primrec.eq.comp hcmp hzero)
        (linearFormComp hsign hone hzero hlp hH) hconst))

private theorem rawSameForm_primrec : Primrec₂ rawSameForm := by
  have hP := isIterate pCode
  have hQ := isIterate qCode
  have ha := exponentCode pCode
  have hb := exponentCode qCode
  have hlp := upperCode pCode
  have hmp := lowerCode pCode
  have hlq := upperCode qCode
  have hmq := lowerCode qCode
  have hba := Primrec.nat_sub.comp hb ha
  have hab := Primrec.nat_sub.comp ha hb
  have hmp' := ordinalAddCodeEffective.comp hmp (omegaMultipleTailCode_primrec.comp hba)
  have hmq' := ordinalAddCodeEffective.comp hmq (omegaMultipleTailCode_primrec.comp hab)
  have hdp := ordinalSubCodeEffective.comp hlp hmp'
  have hdq := ordinalSubCodeEffective.comp hlq hmq'
  have hcmp := rawComparisonPrimitiveRecursive.comp hdp hdq
  have hsign := equalGapCertificateSignEffective.comp (hmp'.pair (hmq'.pair hdp))
  exact Primrec.ite hP
    (Primrec.ite hQ (numericalComparison_primrec.comp ha hb) (Primrec.const 0))
    (Primrec.ite hQ (Primrec.const 2)
      (Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 1)) hsign hcmp))

theorem rawFieldComparisonFormEffective : RawFieldComparisonFormEffective :=
  ⟨rawDistinctForm_primrec,rawSameForm_primrec⟩

end LogicLineages.PermittedControl.FieldComparison
