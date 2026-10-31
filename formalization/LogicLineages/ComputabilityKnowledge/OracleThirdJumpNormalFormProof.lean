module

public import LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormTargets
public import LogicLineages.ComputabilityKnowledge.OracleCertificateProof
public import LogicLineages.ComputabilityKnowledge.OracleJumpProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormProof
open OracleThirdJumpNormalForm OracleThirdJumpNormalFormTargets
open OracleCertificate OracleUniversal OracleJump OraclePiThree OracleRelativeRecursion

private theorem table_agreement (g h : Nat → Nat) (n : Nat)
    (he : ∀ j < n, g (nodeInput j) = h (nodeInput j)) :
    certificateTable g n = certificateTable h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have ht := ih (fun j hj => he j (by omega))
      simp only [certificateTable, ht, he n (by omega)]

theorem finiteOracleAgreement : FiniteOracleAgreement := by
  intro g h c he
  unfold validCertificate
  rw [table_agreement g h (c + 1) (fun j hj => he j (by omega))]

theorem actualHaltingCertificate : ActualHaltingCertificate := by
  intro g q
  change (zeroSearch (certificateTest g) q).Dom ↔ _
  simp [zeroSearch, Nat.rfind_dom, Part.mem_some_iff, eq_comm]

private theorem jump_binary (g : Nat → Nat) (q : Nat) : jump g q = 0 ∨ jump g q = 1 := by
  classical
  unfold jump
  split_ifs <;> simp

private theorem jump_certificate (g : Nat → Nat) (q : Nat) :
    jump g q = 1 ↔ ∃ c, certificateTest g (Nat.pair q c) = 0 :=
  (OracleJumpProof.actualJumpCharacteristic g q).1.trans (actualHaltingCertificate g q)

theorem actualFirstJumpNormalForm : ActualFirstJumpNormalForm := by
  intro q
  simpa [firstJump, firstMatrix] using jump_certificate zeroOracle q

private theorem nodeInput_le (i : Nat) : nodeInput i ≤ i := by
  unfold nodeInput nodeData
  exact (Nat.unpair_left_le _).trans ((Nat.unpair_right_le _).trans
    ((Nat.unpair_right_le _).trans (Nat.sub_le _ _)))

private theorem prefix_get (f : Nat → Nat) (n j : Nat) (hj : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

@[simp] private theorem certificate_pack (c : Nat) (a v : List Nat) :
    traceCertificate (packTrace c a v) = c := by
  simp [traceCertificate, packTrace]

@[simp] private theorem oracle_pack (c : Nat) (a v : List Nat) (j : Nat) :
    traceOracle (packTrace c a v) j = a.getD j 0 := by
  simp [traceOracle, traceAnswers, packTrace, numberList]

@[simp] private theorem witness_pack (c : Nat) (a v : List Nat) (j : Nat) :
    positiveWitness (packTrace c a v) j = v.getD j 0 := by
  simp [positiveWitness, traceWitnesses, packTrace, numberList]

private theorem test_agreement (g h : Nat → Nat) (q c : Nat)
    (he : ∀ j ≤ c, g (nodeInput j) = h (nodeInput j)) :
    certificateTest g (Nat.pair q c) = certificateTest h (Nat.pair q c) := by
  simp only [certificateTest, Nat.unpair_pair, finiteOracleAgreement g h c he]

private theorem trace_accepts_pack (g : Nat → Nat) (q c : Nat) (v : List Nat)
    (hc : certificateTest g (Nat.pair q c) = 0) :
    traceAccepts q (packTrace c ((List.range (c + 1)).map g) v) = true := by
  unfold traceAccepts
  rw [certificate_pack]
  have he : ∀ j ≤ c, traceOracle (packTrace c ((List.range (c + 1)).map g) v)
      (nodeInput j) = g (nodeInput j) := by
    intro j hj
    rw [oracle_pack, prefix_get]
    exact lt_of_le_of_lt (nodeInput_le j) (by omega)
  rw [test_agreement _ g q c he, hc]
  rfl

private theorem trace_accepts_sound (g : Nat → Nat) (q w : Nat)
    (ha : traceAccepts q w = true)
    (he : ∀ j ≤ traceCertificate w, traceOracle w (nodeInput j) = g (nodeInput j)) :
    jump g q = 1 := by
  apply (jump_certificate g q).mpr
  refine ⟨traceCertificate w, ?_⟩
  have h : certificateTest (traceOracle w) (Nat.pair q (traceCertificate w)) = 0 := by
    simpa only [traceAccepts, beq_iff_eq] using ha
  rw [test_agreement _ g q _ he] at h
  exact h

private theorem first_zero (q : Nat) :
    firstJump q = 0 ↔ ∀ c, firstMatrix q c = false := by
  constructor
  · intro h c
    cases hc : firstMatrix q c with
    | false => rfl
    | true =>
        have hh := (actualFirstJumpNormalForm q).mpr ⟨c, hc⟩
        omega
  · intro h
    rcases jump_binary zeroOracle q with hz | ho
    · exact hz
    · obtain ⟨c, hc⟩ := (actualFirstJumpNormalForm q).mp ho
      rw [h c] at hc
      contradiction

private theorem second_local (q w j k : Nat) (hj : j ≤ traceCertificate w)
    (h : secondMatrix q w (Nat.pair j k) = true) :
    if traceOracle w (nodeInput j) = 1 then
      firstMatrix (nodeInput j) (positiveWitness w j) = true
    else traceOracle w (nodeInput j) = 0 ∧ firstMatrix (nodeInput j) k = false := by
  have hh := (Bool.and_eq_true_iff.mp h).2
  by_cases hp : traceOracle w (nodeInput j) = 1
  · simpa only [Nat.unpair_pair, if_pos hj, if_pos hp] using hh
  · simpa only [Nat.unpair_pair, if_pos hj, if_neg hp, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true_eq_eq_false] using hh

theorem actualSecondJumpNormalForm : ActualSecondJumpNormalForm := by
  classical
  intro q
  constructor
  · intro hq
    obtain ⟨c, hc⟩ := (jump_certificate firstJump q).mp hq
    have hex : ∀ j, ∃ v, firstJump (nodeInput j) = 1 → firstMatrix (nodeInput j) v = true := by
      intro j
      by_cases h : firstJump (nodeInput j) = 1
      · obtain ⟨v, hv⟩ := (actualFirstJumpNormalForm (nodeInput j)).mp h
        exact ⟨v, fun _ => hv⟩
      · exact ⟨0, fun hh => False.elim (h hh)⟩
    choose f hf using hex
    let answers := (List.range (c + 1)).map firstJump
    let witnesses := (List.range (c + 1)).map f
    let w := packTrace c answers witnesses
    have ha : traceAccepts q w = true := trace_accepts_pack firstJump q c witnesses hc
    have ho : ∀ j ≤ c, traceOracle w (nodeInput j) = firstJump (nodeInput j) := by
      intro j hj
      rw [oracle_pack, prefix_get]
      exact lt_of_le_of_lt (nodeInput_le j) (by omega)
    have hw : ∀ j ≤ c, positiveWitness w j = f j := by
      intro j hj
      rw [witness_pack, prefix_get]
      omega
    refine ⟨w, ?_⟩
    intro y
    unfold secondMatrix
    rw [ha, Bool.true_and]
    rw [show traceCertificate w = c from certificate_pack c answers witnesses]
    by_cases hj : y.unpair.1 ≤ c
    · rw [if_pos hj]
      dsimp only
      rw [ho _ hj]
      by_cases hp : firstJump (nodeInput y.unpair.1) = 1
      · rw [if_pos hp, hw _ hj]
        exact hf _ hp
      · have hz : firstJump (nodeInput y.unpair.1) = 0 :=
          (jump_binary zeroOracle _).resolve_right hp
        simp [hp, hz, (first_zero _).mp hz]
    · simp [hj]
  · rintro ⟨w, hw⟩
    apply trace_accepts_sound firstJump q w (Bool.and_eq_true_iff.mp (hw 0)).1
    intro j hj
    by_cases hp : traceOracle w (nodeInput j) = 1
    · have hh := second_local q w j 0 hj (hw (Nat.pair j 0))
      rw [if_pos hp] at hh
      exact hp.trans ((actualFirstJumpNormalForm _).mpr ⟨positiveWitness w j, hh⟩).symm
    · have hh := second_local q w j 0 hj (hw (Nat.pair j 0))
      rw [if_neg hp] at hh
      refine hh.1.trans ((first_zero _).mpr ?_).symm
      intro k
      have hk := second_local q w j k hj (hw (Nat.pair j k))
      rw [if_neg hp] at hk
      exact hk.2

private theorem second_zero (q : Nat) :
    secondJump q = 0 ↔ ∀ w, ∃ y, secondMatrix q w y = false := by
  classical
  have hn : secondJump q = 0 ↔ ¬secondJump q = 1 := by
    rcases jump_binary firstJump q with hz | ho <;> simp_all [secondJump]
  rw [hn, actualSecondJumpNormalForm]
  push_neg
  simp only [Bool.not_eq_true]

private theorem third_local (q w j k z : Nat) (hj : j ≤ traceCertificate w)
    (h : thirdMatrix q w (Nat.pair j k) z = true) :
    if traceOracle w (nodeInput j) = 1 then
      secondMatrix (nodeInput j) (positiveWitness w j) k = true
    else traceOracle w (nodeInput j) = 0 ∧ secondMatrix (nodeInput j) k z = false := by
  have hh := (Bool.and_eq_true_iff.mp h).2
  by_cases hp : traceOracle w (nodeInput j) = 1
  · simpa only [Nat.unpair_pair, if_pos hj, if_pos hp] using hh
  · simpa only [Nat.unpair_pair, if_pos hj, if_neg hp, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true_eq_eq_false] using hh

theorem actualThirdJumpNormalForm : ActualThirdJumpNormalForm := by
  classical
  intro q
  constructor
  · intro hq
    obtain ⟨c, hc⟩ := (jump_certificate secondJump q).mp hq
    have hex : ∀ j, ∃ v, secondJump (nodeInput j) = 1 →
        ∀ k, secondMatrix (nodeInput j) v k = true := by
      intro j
      by_cases h : secondJump (nodeInput j) = 1
      · obtain ⟨v, hv⟩ := (actualSecondJumpNormalForm (nodeInput j)).mp h
        exact ⟨v, fun _ => hv⟩
      · exact ⟨0, fun hh => False.elim (h hh)⟩
    choose f hf using hex
    let answers := (List.range (c + 1)).map secondJump
    let witnesses := (List.range (c + 1)).map f
    let w := packTrace c answers witnesses
    have ha : traceAccepts q w = true := trace_accepts_pack secondJump q c witnesses hc
    have ho : ∀ j ≤ c, traceOracle w (nodeInput j) = secondJump (nodeInput j) := by
      intro j hj
      rw [oracle_pack, prefix_get]
      exact lt_of_le_of_lt (nodeInput_le j) (by omega)
    have hw : ∀ j ≤ c, positiveWitness w j = f j := by
      intro j hj
      rw [witness_pack, prefix_get]
      omega
    refine ⟨w, ?_⟩
    intro y
    by_cases hj : y.unpair.1 ≤ c
    · by_cases hp : secondJump (nodeInput y.unpair.1) = 1
      · refine ⟨0, ?_⟩
        unfold thirdMatrix
        rw [ha, Bool.true_and]
        rw [show traceCertificate w = c from certificate_pack c answers witnesses]
        rw [if_pos hj]
        dsimp only
        rw [ho _ hj, if_pos hp, hw _ hj]
        exact hf _ hp _
      · have hz : secondJump (nodeInput y.unpair.1) = 0 :=
          (jump_binary firstJump _).resolve_right hp
        obtain ⟨z, hz'⟩ := (second_zero _).mp hz y.unpair.2
        refine ⟨z, ?_⟩
        unfold thirdMatrix
        rw [ha, Bool.true_and]
        rw [show traceCertificate w = c from certificate_pack c answers witnesses]
        rw [if_pos hj]
        dsimp only
        rw [ho _ hj, if_neg hp]
        simp [hz, hz']
    · refine ⟨0, ?_⟩
      unfold thirdMatrix
      rw [ha, Bool.true_and]
      rw [show traceCertificate w = c from certificate_pack c answers witnesses]
      simp [hj]
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz⟩ := hw 0
    apply trace_accepts_sound secondJump q w (Bool.and_eq_true_iff.mp hz).1
    intro j hj
    by_cases hp : traceOracle w (nodeInput j) = 1
    · refine hp.trans ((actualSecondJumpNormalForm _).mpr ⟨positiveWitness w j, ?_⟩).symm
      intro k
      obtain ⟨z, hz⟩ := hw (Nat.pair j k)
      have hh := third_local q w j k z hj hz
      rwa [if_pos hp] at hh
    · obtain ⟨z, hz⟩ := hw (Nat.pair j 0)
      have hh := third_local q w j 0 z hj hz
      rw [if_neg hp] at hh
      refine hh.1.trans ((second_zero _).mpr ?_).symm
      intro k
      obtain ⟨z, hz⟩ := hw (Nat.pair j k)
      have hk := third_local q w j k z hj hz
      rw [if_neg hp] at hk
      exact ⟨z, hk.2⟩

theorem actualThirdJumpComplement : ActualThirdJumpComplement := by
  classical
  intro q
  have hn : thirdJump q = 0 ↔ ¬thirdJump q = 1 := by
    rcases jump_binary secondJump q with hz | ho <;> simp_all [thirdJump]
  rw [hn, actualThirdJumpNormalForm]
  push_neg
  simp only [thirdComplementMatrix, Bool.not_eq_true_eq_eq_false, Bool.not_eq_true]

private theorem pr_nodeData : Primrec nodeData :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
private theorem pr_nodeCode : Primrec nodeCode := Primrec.fst.comp (Primrec.unpair.comp pr_nodeData)
private theorem pr_nodeInput : Primrec nodeInput :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData)))

private theorem pr_finiteTable : Primrec (fun a : List Nat × Nat =>
    certificateTable (fun q => a.1.getD q 0) a.2) := by
  have hi : Primrec (fun a : List Nat × Nat × List Bool => a.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun a : List Nat × Nat × List Bool => a.2.2) :=
    Primrec.snd.comp Primrec.snd
  have ha := (Primrec.list_getD 0).comp Primrec.fst (pr_nodeInput.comp hi)
  have hs := OracleCertificateProof.primitiveRecursiveCertificateStep.comp (ha.pair (hi.pair hl))
  have hu := Primrec.list_concat.comp hl hs
  have hr := Primrec.nat_rec (Primrec.const ([] : List Bool)) hu.to₂
  apply (hr.comp Primrec.fst Primrec.snd).of_eq
  rintro ⟨xs, n⟩
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.rec_add_one, certificateTable, ih, List.concat_eq_append]

private theorem pr_finiteCertificate : Primrec (fun a : List Nat × Nat =>
    validCertificate (fun q => a.1.getD q 0) a.2) := by
  exact (Primrec.list_getD false).comp
    (pr_finiteTable.comp (Primrec.fst.pair (Primrec.succ.comp Primrec.snd))) Primrec.snd

private theorem pr_finiteTest : Primrec (fun a : List Nat × Nat × Nat =>
    certificateTest (fun q => a.1.getD q 0) (Nat.pair a.2.1 a.2.2) == 0) := by
  have hq : Primrec (fun a : List Nat × Nat × Nat => a.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun a : List Nat × Nat × Nat => a.2.2) := Primrec.snd.comp Primrec.snd
  have hv := pr_finiteCertificate.comp (Primrec.fst.pair hc)
  have hec := Primrec.beq.comp (pr_nodeCode.comp hc) (Primrec.fst.comp (Primrec.unpair.comp hq))
  have hei := Primrec.beq.comp (pr_nodeInput.comp hc) (Primrec.snd.comp (Primrec.unpair.comp hq))
  apply (Primrec.and.comp (Primrec.and.comp hv hec) hei).of_eq
  intro a
  apply Bool.eq_iff_iff.mpr
  simp [certificateTest, Bool.and_eq_true, and_assoc]

private theorem pr_numberList : Primrec numberList :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])
private theorem pr_traceCertificate : Primrec traceCertificate := Primrec.fst.comp Primrec.unpair
private theorem pr_traceAnswers : Primrec traceAnswers :=
  pr_numberList.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
private theorem pr_traceWitnesses : Primrec traceWitnesses :=
  pr_numberList.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
private theorem pr_traceOracle : Primrec (fun a : Nat × Nat => traceOracle a.1 a.2) :=
  (Primrec.list_getD 0).comp (pr_traceAnswers.comp Primrec.fst) Primrec.snd
private theorem pr_positiveWitness : Primrec (fun a : Nat × Nat => positiveWitness a.1 a.2) :=
  (Primrec.list_getD 0).comp (pr_traceWitnesses.comp Primrec.fst) Primrec.snd
private theorem pr_traceAccepts : Primrec (fun a : Nat × Nat => traceAccepts a.1 a.2) := by
  have h := pr_finiteTest.comp ((pr_traceAnswers.comp Primrec.snd).pair
    (Primrec.fst.pair (pr_traceCertificate.comp Primrec.snd)))
  apply h.of_eq
  intro a
  dsimp only [traceAccepts, traceOracle]
  rfl

private theorem pr_firstMatrix : Primrec (fun a : Nat × Nat => firstMatrix a.1 a.2) := by
  have h := pr_finiteTest.comp ((Primrec.const ([] : List Nat)).pair (Primrec.fst.pair Primrec.snd))
  exact h.of_eq (fun _ => rfl)

private theorem pr_secondMatrix : Primrec (fun a : Nat × Nat × Nat => secondMatrix a.1 a.2.1 a.2.2) := by
  have hw : Primrec (fun a : Nat × Nat × Nat => a.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun a : Nat × Nat × Nat => a.2.2) := Primrec.snd.comp Primrec.snd
  have hj := Primrec.fst.comp (Primrec.unpair.comp hy)
  have hk := Primrec.snd.comp (Primrec.unpair.comp hy)
  have hn := pr_nodeInput.comp hj
  have ha := pr_traceOracle.comp (hw.pair hn)
  have hv := pr_positiveWitness.comp (hw.pair hj)
  have hp := pr_firstMatrix.comp (hn.pair hv)
  have hneg := Primrec.and.comp (Primrec.beq.comp ha (Primrec.const 0))
    (Primrec.not.comp (pr_firstMatrix.comp (hn.pair hk)))
  have hbranch := Primrec.ite (Primrec.eq.comp ha (Primrec.const 1)) hp hneg
  have hlocal := Primrec.ite (Primrec.nat_le.comp hj (pr_traceCertificate.comp hw)) hbranch (Primrec.const true)
  have h := Primrec.and.comp (pr_traceAccepts.comp (Primrec.fst.pair hw)) hlocal
  apply h.of_eq
  intro a
  dsimp only [secondMatrix]

private theorem pr_thirdMatrix : Primrec (fun a : Nat × Nat × Nat × Nat =>
    thirdMatrix a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hw : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hz : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hj := Primrec.fst.comp (Primrec.unpair.comp hy)
  have hk := Primrec.snd.comp (Primrec.unpair.comp hy)
  have hn := pr_nodeInput.comp hj
  have ha := pr_traceOracle.comp (hw.pair hn)
  have hv := pr_positiveWitness.comp (hw.pair hj)
  have hp := pr_secondMatrix.comp (hn.pair (hv.pair hk))
  have hneg := Primrec.and.comp (Primrec.beq.comp ha (Primrec.const 0))
    (Primrec.not.comp (pr_secondMatrix.comp (hn.pair (hk.pair hz))))
  have hbranch := Primrec.ite (Primrec.eq.comp ha (Primrec.const 1)) hp hneg
  have hlocal := Primrec.ite (Primrec.nat_le.comp hj (pr_traceCertificate.comp hw)) hbranch (Primrec.const true)
  have h := Primrec.and.comp (pr_traceAccepts.comp (Primrec.fst.pair hw)) hlocal
  apply h.of_eq
  intro a
  dsimp only [thirdMatrix]

theorem explicitMatricesPrimitiveRecursive : ExplicitMatricesPrimitiveRecursive :=
  ⟨pr_firstMatrix, pr_secondMatrix, Primrec.not.comp pr_thirdMatrix⟩

theorem recursiveActualThirdJumpComplement : RecursiveActualThirdJumpComplement := by
  refine ⟨thirdComplementMatrix, explicitMatricesPrimitiveRecursive.2.2.to_comp, ?_⟩
  intro q
  exact (actualThirdJumpComplement q).symm

end LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormProof
