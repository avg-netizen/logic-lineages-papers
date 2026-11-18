module
public import LogicLineages.PermittedControl.ThresholdNumericProgramsProof
public import LogicLineages.PermittedControl.ThresholdNumericCalibrationProof
public import LogicLineages.PermittedControl.FixedEntryProgramProof
public import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem threshold_partrec_if {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p)
    {f g : α → Part β} (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun z => if p z then f z else g z) :=
  (Partrec.cond hp.decide.to_comp hf hg).of_eq (by intro z; by_cases h : p z <;> simp [h])

 theorem thresholdProgram_partrec (f : Nat → Nat) (hf : Computable f) : Partrec (thresholdProgram f) := by
  have hlp : Primrec (fun z : IntervalPairCodes×(Nat×Nat) => z.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hmp : Primrec (fun z : IntervalPairCodes×(Nat×Nat) => z.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hlq : Primrec (fun z : IntervalPairCodes×(Nat×Nat) => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hmq : Primrec (fun z : IntervalPairCodes×(Nat×Nat) => z.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec (fun z : IntervalPairCodes×(Nat×Nat) => z.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun z : IntervalPairCodes×(Nat×Nat) => z.2.2) := Primrec.snd.comp Primrec.snd
  have hdp := ordinalSubCodeEffective.comp hlp hmp
  have hdq := ordinalSubCodeEffective.comp hlq hmq
  have hg := rawComparisonPrimitiveRecursive.comp hdq hdp
  have heqsign := equalGapCertificateSignEffective.comp (hmp.pair (hmq.pair hdp))
  have hleftsign := equalGapCertificateSignEffective.comp (hmp.pair (hmq.pair hdq))
  have hrightsign := equalGapCertificateSignEffective.comp (hmq.pair (hmp.pair hdp))
  have heq := Primrec.ite (Primrec.nat_lt.comp hx hy) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_lt.comp hy hx) (Primrec.const 2) heqsign)
  have hleft := (fixedEntryProgramEffectivity f hf).1.comp
    (hlp.pair ((ordinalAddCodeEffective.comp hmp hdq).pair hx)).to_comp
  have hright := (fixedEntryProgramEffectivity f hf).1.comp
    (hlq.pair ((ordinalAddCodeEffective.comp hmq hdp).pair hy)).to_comp
  have hleftmap : Primrec (fun z : (IntervalPairCodes×(Nat×Nat))×(Nat×Nat) =>
      inverseTableDecisionCode (equalGapCertificateCode z.1.1.1.2 z.1.1.2.2
        (ordinalSubCode z.1.1.2.1 z.1.1.2.2)) z.1.2.2 z.2.1) :=
    inverseTableDecisionCode_primrec.comp ((hleftsign.comp Primrec.fst).pair
      ((hy.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
  have hrightmap : Primrec (fun z : (IntervalPairCodes×(Nat×Nat))×(Nat×Nat) =>
      reverseComparisonCode (inverseTableDecisionCode
        (equalGapCertificateCode z.1.1.2.2 z.1.1.1.2 (ordinalSubCode z.1.1.1.1 z.1.1.1.2)) z.1.2.1 z.2.1)) :=
    reverseComparisonCode_primrec.comp (inverseTableDecisionCode_primrec.comp
      ((hrightsign.comp Primrec.fst).pair ((hx.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))))
  exact threshold_partrec_if (Primrec.eq.comp hg (Primrec.const 1)) heq.to_comp.partrec
    (threshold_partrec_if (Primrec.eq.comp hg (Primrec.const 0))
      (hleft.map hleftmap.to_comp.to₂) (hright.map hrightmap.to_comp.to₂))

 theorem translatedThresholdProgram_partrec (f : Nat → Nat) (hf : Computable f) : Partrec (translatedThresholdProgram f) := by
  have hp : Primrec (fun z : (IntervalPairCodes×SignedShiftCodes)×(Nat×Nat) => z.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun z : (IntervalPairCodes×SignedShiftCodes)×(Nat×Nat) => z.1.2) := Primrec.snd.comp Primrec.fst
  have hx : Primrec (fun z : (IntervalPairCodes×SignedShiftCodes)×(Nat×Nat) => z.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun z : (IntervalPairCodes×SignedShiftCodes)×(Nat×Nat) => z.2.2) := Primrec.snd.comp Primrec.snd
  have hu := signedTranslateCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp hs)) hx
  have hv := signedTranslateCode_primrec.comp (Primrec.snd.comp (Primrec.fst.comp hs)) hy
  have hb := (thresholdProgram_partrec f hf).comp (hp.pair (hu.pair hv)).to_comp
  have ha := Primrec.fst.comp (Primrec.snd.comp hs)
  have hc := Primrec.snd.comp (Primrec.snd.comp hs)
  have houtput : Primrec (fun z : ((IntervalPairCodes×SignedShiftCodes)×(Nat×Nat))×Nat =>
      if z.2=1 then signedComparisonCode z.1.1.2.2.1 z.1.1.2.2.2 else z.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (signedComparisonCode_primrec.comp (ha.comp Primrec.fst) (hc.comp Primrec.fst)) Primrec.snd
  exact hb.map houtput.to_comp.to₂

 theorem thresholdProgramsEffective : Targets.ThresholdProgramsEffective :=
  ⟨thresholdTailCode_primrec,translatedThresholdTailCode_primrec,
    fun f hf => ⟨thresholdProgram_partrec f hf,translatedThresholdProgram_partrec f hf⟩,
    signedComparisonCode_correct,signedTranslateCode_correct,signedOffsetMagnitudeCode_correct⟩

end LogicLineages.PermittedControl
