module
public import LogicLineages.PermittedControl.ThresholdTargets
public import LogicLineages.PermittedControl.OrdinalEndpointCodeProof
public import LogicLineages.PermittedControl.EqualGapCertificateCodeProof
public import LogicLineages.PermittedControl.GapInputFoundationProof
public import LogicLineages.PermittedControl.OutputOffsetProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem inverseTableTailCode_primrec {α : Type*} [Primcodable α]
    {l m n d b : α → Nat} (hl : Primrec l) (hm : Primrec m) (hn : Primrec n)
    (hd : Primrec d) (hb : Primrec b) : Primrec (fun z => inverseTableTailCode (l z) (m z) (n z) (d z) (b z)) := by
  have hr : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hk := ordinalAddCodeEffective.comp hm hd
  have hq := ordinalAddCodeEffective.comp hn hd
  have hguard := Primrec.nat_max.comp (Primrec.const 2)
    (Primrec.nat_max.comp (hr.comp hl) (Primrec.nat_max.comp (hr.comp hk) (hr.comp hm)))
  have hg : Primrec encodedGapInputTail := by
    have h1 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.1) := Primrec.fst
    have h2 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.1) := Primrec.fst.comp Primrec.snd
    have h3 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have h4 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have h5 : Primrec (fun z : Nat×Nat×Nat×Nat×Nat => z.2.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have he : Primrec encodedGapInputTail :=
      Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 2) (hr.comp h1)) (hr.comp h3))
        (Primrec.nat_max.comp (Primrec.const 1) (Primrec.nat_max.comp (hr.comp h2) (hr.comp h4))))
        (Primrec.nat_mul.comp (Primrec.const 2) h5)
    exact he
  have hleft := hg.comp (hk.pair (hm.pair (hq.pair (hn.pair (Primrec.const 0)))))
  have hright := hg.comp (hq.pair (hn.pair (hk.pair (hm.pair (Primrec.const 0)))))
  have hcert := equalGapCertificateTailEffective.comp (hm.pair (hn.pair (hd.pair hb)))
  exact Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_max.comp hguard (Primrec.nat_max.comp hleft (Primrec.nat_max.comp hright hcert)))

 theorem thresholdTailCode_primrec : Primrec (fun z : IntervalPairCodes×Nat => thresholdTailCode z.1 z.2) := by
  have hlp : Primrec (fun z : IntervalPairCodes×Nat => z.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hmp : Primrec (fun z : IntervalPairCodes×Nat => z.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hlq : Primrec (fun z : IntervalPairCodes×Nat => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hmq : Primrec (fun z : IntervalPairCodes×Nat => z.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.nat_max.comp
    (inverseTableTailCode_primrec hlp hmp hmq (ordinalSubCodeEffective.comp hlq hmq) Primrec.snd)
    (inverseTableTailCode_primrec hlq hmq hmp (ordinalSubCodeEffective.comp hlp hmp) Primrec.snd)

 theorem signedOffsetMagnitudeCode_primrec : Primrec signedOffsetMagnitudeCode :=
  Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))

 theorem signedTranslateCode_primrec : Primrec₂ signedTranslateCode :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0))
    (Primrec.nat_add.comp Primrec.snd (Primrec.nat_div.comp Primrec.fst (Primrec.const 2)))
    (Primrec.nat_sub.comp Primrec.snd (Primrec.succ.comp (Primrec.nat_div.comp Primrec.fst (Primrec.const 2))))

 theorem signedComparisonCode_primrec : Primrec₂ signedComparisonCode := by
  have ha := Primrec.nat_div.comp (Primrec.fst : Primrec (fun p : Nat×Nat => p.1)) (Primrec.const 2)
  have hb := Primrec.nat_div.comp (Primrec.snd : Primrec (fun p : Nat×Nat => p.2)) (Primrec.const 2)
  have hpa := Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)) (Primrec.const 0)
  have hpb := Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  exact Primrec.ite hpa
    (Primrec.ite hpb (numericalComparison_primrec.comp ha hb) (Primrec.const 2))
    (Primrec.ite hpb (Primrec.const 0) (numericalComparison_primrec.comp hb ha))

 theorem reverseComparisonCode_primrec : Primrec reverseComparisonCode :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const 0) (Primrec.const 1))

 theorem inverseTableDecisionCode_primrec : Primrec (fun p : Nat×Nat×Nat => inverseTableDecisionCode p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : Nat×Nat×Nat => p.1) := Primrec.fst
  have hy : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hh : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp hs (Primrec.const 1)) (numericalComparison_primrec.comp hh hy)
    (Primrec.ite (Primrec.eq.comp hs (Primrec.const 2))
      (Primrec.ite (Primrec.nat_le.comp hy hh) (Primrec.const 2) (Primrec.const 0))
      (Primrec.ite (Primrec.nat_lt.comp hy hh) (Primrec.const 2) (Primrec.const 0)))

 theorem translatedThresholdTailCode_primrec : Primrec
    (fun z : (IntervalPairCodes×SignedShiftCodes)×Nat => translatedThresholdTailCode z.1.1 z.1.2 z.2) := by
  have ht := thresholdTailCode_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hs : Primrec (fun z : (IntervalPairCodes×SignedShiftCodes)×Nat => z.1.2) := Primrec.snd.comp Primrec.fst
  have hr := signedOffsetMagnitudeCode_primrec.comp (Primrec.fst.comp (Primrec.fst.comp hs))
  have hu := signedOffsetMagnitudeCode_primrec.comp (Primrec.snd.comp (Primrec.fst.comp hs))
  have ha := signedOffsetMagnitudeCode_primrec.comp (Primrec.fst.comp (Primrec.snd.comp hs))
  have hb := signedOffsetMagnitudeCode_primrec.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp ht hr) hu) ha) hb) (Primrec.const 2)

end LogicLineages.PermittedControl
