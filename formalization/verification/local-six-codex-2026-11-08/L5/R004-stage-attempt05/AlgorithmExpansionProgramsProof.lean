module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmResidualProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
open PolynomialGraphCompletion WordGuardCompletion CounterWordGuardCompletion Algorithm

theorem counterWord_primitive : Primrec (fun p : Word × Nat × Nat => counterWord p.1 p.2.1 p.2.2) :=
  Primrec.list_append.comp Primrec.fst
    (Primrec.list_cons.comp (counterLetter_primitive.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 3))
      (Primrec.snd.comp Primrec.snd)) (Primrec.const []))

theorem leaderValueWord_primitive :
    Primrec (fun p : Word × Nat × Nat => leaderValueWord p.1 p.2.1 p.2.2) :=
  Primrec.list_append.comp
    (Primrec.list_append.comp Primrec.fst (CounterWordGuardCompletion.Proof.leaderWord_primitive.comp Primrec.snd))
    (Primrec.const [phiLetter])

theorem residualPrefixWords_primitive : Primrec (fun p : Word × List (Nat × Word) =>
    p.2.map (fun q => p.1++q.2)) :=
  Primrec.list_map Primrec.snd
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂

theorem expansionWords_primitive :
    Primrec (fun p : Word × Nat × Nat => expansionWords p.1 p.2.1 p.2.2) :=
  Primrec.list_cons.comp counterWord_primitive
    (Primrec.list_cons.comp leaderValueWord_primitive
      (residualPrefixWords_primitive.comp
        (Primrec.fst.pair (residualWords_primitive.comp Primrec.snd))))

theorem expansionTail_primitive :
    Primrec (fun p : Word × Nat × Nat => expansionTail p.1 p.2.1 p.2.2) :=
  Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp
      (Primrec.fst.pair (CounterWordGuardCompletion.Proof.leaderTail_primitive.comp Primrec.snd)))
    (foldMax_primitive.comp (Primrec.list_map expansionWords_primitive
      (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.snd).to₂))

theorem counterBoundThreshold_primitive :
    Primrec (fun p : Nat × Nat => CounterLeaderBounds.threshold p.1 p.2) :=
  Primrec.nat_max.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 3)))) (Primrec.const 1))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 10))

theorem sourceTail_primitive : Primrec sourceTail := by
  have hargs := innerWord_primitive.pair (counterIndex_primitive.pair mass_primitive)
  have he := expansionTail_primitive.comp hargs
  have hr := WordGuardCompletion.Proof.reachTail_primitive.comp
    (innerWord_primitive.pair (counterBoundThreshold_primitive.comp
      (counterIndex_primitive.pair mass_primitive)))
  have hcounter := Primrec.nat_max.comp he hr
  have hordinary := Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp head_primitive) (Primrec.const 1))
    (WordGuardCompletion.Proof.wordTail_primitive.comp innerWord_primitive)
    (RangePhiFactorization.Proof.wordFactorTail_primitive.comp (innerWord_primitive.pair head_primitive))
  have hright := Primrec.cond isCounter_primitive hcounter hordinary
  apply (Primrec.nat_max.comp
    (WordGuardCompletion.Proof.wordTail_primitive.comp (Primrec.snd.comp Primrec.snd)) hright).of_eq
  intro a
  cases hc : isCounter a <;> simp [sourceTail,hc]

theorem collisionTail_primitive : Primrec₂ collisionTail := by
  have ha : Primrec (fun p : Item × Item => p.1) := Primrec.fst
  have hb : Primrec (fun p : Item × Item => p.2) := Primrec.snd
  have hsa := CounterWordGuardCompletion.Proof.scalarTail_primitive.comp
    ((counterIndex_primitive.comp ha).pair ((mass_primitive.comp ha).pair
      ((mass_primitive.comp hb).pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))))
  have hsb := CounterWordGuardCompletion.Proof.scalarTail_primitive.comp
    ((counterIndex_primitive.comp hb).pair ((mass_primitive.comp hb).pair
      ((mass_primitive.comp ha).pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))))
  have hra := WordGuardCompletion.Proof.reachTail_primitive.comp ((innerWord_primitive.comp ha).pair hsa)
  have hrb := WordGuardCompletion.Proof.reachTail_primitive.comp ((innerWord_primitive.comp hb).pair hsb)
  apply (Primrec.cond (Primrec.and.comp (isCounter_primitive.comp ha) (isCounter_primitive.comp hb))
    (Primrec.nat_max.comp hra hrb) (Primrec.const 0)).of_eq
  intro p
  cases hca : isCounter p.1 <;> cases hcb : isCounter p.2 <;> simp [collisionTail,hca,hcb]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
