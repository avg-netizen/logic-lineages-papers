module
public import LogicLineages.OrdinalComparison.WWEncodedScalarTargets
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldProof
public import LogicLineages.OrdinalComparison.WWFixedShiftProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

theorem scalarCodeInstantiationPrimitiveRecursive : Targets.ScalarCodeInstantiationPrimitiveRecursive := by
  let children : Nat × List Nat → List (Nat × List Nat) := fun p =>
    if p.1 % 4 = 0 then [] else if p.1 % 4 = 1 then [] else
      [((p.1 / 4).unpair.1, p.2), ((p.1 / 4).unpair.2, p.2)]
  let assemble : (Nat × List Nat) → List Nat → Option Nat := fun p rs => some
    (if p.1 % 4 = 0 then p.1 else if p.1 % 4 = 1 then 4 * (p.2.getD (p.1 / 4) 0 + 1)
    else if p.1 % 4 = 2 then 4 * Nat.pair (rs.getD 0 0) (rs.getD 1 0) + 2
    else 4 * Nat.pair (p.1 / 4).unpair.1 (rs.getD 1 0) + 3)
  have hm : Primrec (fun p : Nat × List Nat => p.1 % 4) :=
    Primrec.nat_mod.comp Primrec.fst (Primrec.const 4)
  have hd : Primrec (fun p : Nat × List Nat => p.1 / 4) :=
    Primrec.nat_div.comp Primrec.fst (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hc : Primrec children :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const [])
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (Primrec.const [])
        (Primrec.list_cons.comp (hl.pair Primrec.snd)
          (Primrec.list_cons.comp (hr.pair Primrec.snd) (Primrec.const []))))
  have ha : Primrec₂ assemble := by
    have he (k : Nat) : PrimrecPred (fun p : (Nat × List Nat) × List Nat => p.1.1 % 4 = k) := (Primrec.eq.comp hm (Primrec.const k)).comp Primrec.fst
    have hvar : Primrec (fun p : (Nat × List Nat) × List Nat => p.1.2.getD (p.1.1 / 4) 0) := (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) (hd.comp Primrec.fst)
    have hget (k : Nat) : Primrec (fun p : (Nat × List Nat) × List Nat => p.2.getD k 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const k)
    apply Primrec.option_some.comp
    exact Primrec.ite (he 0) (Primrec.fst.comp Primrec.fst)
      (Primrec.ite (he 1)
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.succ.comp hvar))
        (Primrec.ite (he 2)
          (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
            (Primrec₂.natPair.comp (hget 0) (hget 1))) (Primrec.const 2))
          (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
            (Primrec₂.natPair.comp (hl.comp Primrec.fst) (hget 1))) (Primrec.const 3))))
  apply Primrec.nat_omega_rec' (fun p : Nat × List Nat => instantiateScalarCode p.2 p.1)
    Primrec.fst hc ha
  · intro p q hq
    by_cases h0 : p.1 % 4 = 0
    · simp [children, h0] at hq
    by_cases h1 : p.1 % 4 = 1
    · simp [children, h0, h1] at hq
    have hn : 0 < p.1 := by omega
    have hdlt := Nat.div_lt_self hn (show 1 < 4 by decide)
    simp only [children, if_neg h0, if_neg h1, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hdlt
    · exact (Nat.unpair_right_le _).trans_lt hdlt
  · intro p
    rw [instantiateScalarCode]
    by_cases h0 : p.1 % 4 = 0
    · simp [children, assemble, h0]
    by_cases h1 : p.1 % 4 = 1
    · simp [children, assemble, h0, h1]
    simp [children, assemble, h0, h1]

private theorem instantiate_constant (xs : List Nat) (n : Nat) :
    instantiateScalarCode xs (4*n) = 4*n := by
  rw [instantiateScalarCode]
  simp

private theorem instantiate_variable (xs : List Nat) (n : Nat) :
    instantiateScalarCode xs (4*n+1) = 4*(xs.getD n 0+1) := by
  have hm : (4*n+1)%4=1 := by omega
  have hd : (4*n+1)/4=n := by omega
  rw [instantiateScalarCode]
  simp [hm, hd]

private theorem instantiate_add (xs : List Nat) (a b : Nat) :
    instantiateScalarCode xs (4*Nat.pair a b+2) =
      4*Nat.pair (instantiateScalarCode xs a) (instantiateScalarCode xs b)+2 := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [instantiateScalarCode]
  simp [hm, hd]

private theorem instantiate_shift (xs : List Nat) (h a : Nat) :
    instantiateScalarCode xs (4*Nat.pair h a+3) =
      4*Nat.pair h (instantiateScalarCode xs a)+3 := by
  have hm : (4*Nat.pair h a+3)%4=3 := by omega
  have hd : (4*Nat.pair h a+3)/4=Nat.pair h a := by omega
  rw [instantiateScalarCode]
  simp [hm, hd]

theorem scalarCodeInstantiationCorrect : Targets.ScalarCodeInstantiationCorrect := by
  intro ι index s xs
  induction s with
  | one => exact instantiate_constant xs 1
  | var x => exact instantiate_variable xs (index x)
  | add a b iha ihb => simp only [scalarCode, instantiate_add, iha, ihb, scalarGround, positiveExprEncode]
  | shift c a ih => simp only [scalarCode, instantiate_shift, ih, scalarGround, positiveExprEncode]

theorem encodedScalarComputable : Targets.EncodedScalarComputable :=
  encodedPositiveFoldComputable.comp scalarCodeInstantiationPrimitiveRecursive.to_comp

private theorem ground_value {ι : Type} (index : ι → Nat) (xs : List Nat) (s : Scalar ι) :
    actualFixedLimitProfileEval (scalarGround index xs s) 0 =
      s.value (fun i => xs.getD (index i) 0 + 1) := by
  induction s with
  | one => rfl
  | var x => rfl
  | add a b iha ihb => simp only [scalarGround, actualFixedLimitProfileEval, Scalar.value, iha, ihb]
  | shift c a ih =>
    have he : (scalarHeadNote c).1.repr = fixedHead c := by
      rw [scalarHeadNote, naturalProductDenotation]
      simp [fixedHead, ONote.repr]
    simp only [scalarGround, actualFixedLimitProfileEval, Scalar.value, actualProfileHead, ih, he]

theorem encodedScalarSourceCorrect : Targets.EncodedScalarSourceCorrect := by
  intro ι index s xs
  rw [encodedScalarValue, scalarCodeInstantiationCorrect, encodedPositiveFoldSourceCorrect]
  exact ground_value index xs s
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
