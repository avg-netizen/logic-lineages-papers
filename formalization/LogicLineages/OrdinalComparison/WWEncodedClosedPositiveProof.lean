module
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveTargets
public import LogicLineages.OrdinalComparison.WWEncodedBaseTwoProof
public import LogicLineages.OrdinalComparison.EncodedNaturalProductProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

private theorem eval_add (a b : Nat) :
    encodedClosedPositive (4*Nat.pair a b+2) =
      encodedNaturalSum (encodedClosedPositive a) (encodedClosedPositive b) := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [encodedClosedPositive]
  simp [hm, hd]

private theorem eval_emul (a b : Nat) :
    encodedClosedPositive (4*Nat.pair a b+3) =
      encodedNaturalProduct (encodedBaseTwoPower (encodedClosedPositive a)) (encodedClosedPositive b) := by
  have hm : (4*Nat.pair a b+3)%4=3 := by omega
  have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
  rw [encodedClosedPositive]
  simp [hm, hd]

theorem encodedClosedPositiveCorrect : Targets.EncodedClosedPositiveCorrect := by
  intro c
  induction c with
  | one => simp [closedPositiveCode, encodedClosedPositive]
  | omega => simp [closedPositiveCode, encodedClosedPositive]
  | add a b iha ihb =>
    rw [closedPositiveCode, eval_add, iha, ihb, encodedNaturalSumCorrect a.evaluate.1 b.evaluate.1]
    rfl
  | emul a b iha ihb =>
    rw [closedPositiveCode, eval_emul, iha, ihb, encodedBaseTwoPowerCorrect a.evaluate,
      encodedNaturalProductCorrect]
    rfl

theorem encodedClosedPositivePrimitiveRecursive : Targets.EncodedClosedPositivePrimitiveRecursive := by
  let children : Nat → List Nat := fun n => if n%4=0 then [] else if n%4=1 then [] else
    [(n/4).unpair.1, (n/4).unpair.2]
  let assemble : Nat → List Nat → Option Nat := fun n rs => some
    (if n%4=0 then rawNoteEncode ClosedPositive.one.evaluate.1
    else if n%4=1 then rawNoteEncode ClosedPositive.omega.evaluate.1
    else if n%4=2 then encodedNaturalSum (rs.getD 0 0) (rs.getD 1 0)
    else encodedNaturalProduct (encodedBaseTwoPower (rs.getD 0 0)) (rs.getD 1 0))
  have hm : Primrec (fun n : Nat => n%4) := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
  have hd : Primrec (fun n : Nat => n/4) := Primrec.nat_div.comp Primrec.id (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hc : Primrec children :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const [])
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (Primrec.const [])
        (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const []))))
  have ha : Primrec₂ assemble := by
    have he (k : Nat) : PrimrecPred (fun p : Nat × List Nat => p.1%4=k) :=
      (Primrec.eq.comp hm (Primrec.const k)).comp Primrec.fst
    have hg (k : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD k 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite (he 0)
      (Primrec.const (rawNoteEncode ClosedPositive.one.evaluate.1))
      (Primrec.ite (he 1) (Primrec.const (rawNoteEncode ClosedPositive.omega.evaluate.1))
        (Primrec.ite (he 2) (encodedNaturalSumPrimitiveRecursive.comp (hg 0) (hg 1))
          (encodedNaturalProductPrimitiveRecursive.comp
            (encodedBaseTwoPowerPrimitiveRecursive.comp (hg 0)) (hg 1)))))
  apply Primrec.nat_omega_rec' encodedClosedPositive Primrec.id hc ha
  · intro n t ht
    by_cases h0 : n%4=0
    · simp [children, h0] at ht
    by_cases h1 : n%4=1
    · simp [children, h0, h1] at ht
    have hn : 0<n := by omega
    have hdiv := Nat.div_lt_self hn (show 1<4 by decide)
    simp only [children, if_neg h0, if_neg h1, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hdiv
    · exact (Nat.unpair_right_le _).trans_lt hdiv
  · intro n
    rw [encodedClosedPositive]
    by_cases h0 : n%4=0
    · simp [children, assemble, h0]
    by_cases h1 : n%4=1
    · simp [children, assemble, h0, h1]
    simp [children, assemble, h0, h1]

theorem encodedClosedHeadCorrect : Targets.EncodedClosedHeadCorrect := by
  intro c
  rw [encodedClosedHead, encodedClosedPositiveCorrect c, encodedNaturalProductCorrect]
  rfl

theorem encodedClosedHeadPrimitiveRecursive : Targets.EncodedClosedHeadPrimitiveRecursive :=
  encodedNaturalProductPrimitiveRecursive.comp
    (Primrec.const (rawNoteEncode ClosedPositive.omega.evaluate.1)) encodedClosedPositivePrimitiveRecursive
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
