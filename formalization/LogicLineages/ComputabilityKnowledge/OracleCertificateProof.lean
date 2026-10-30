module

public import Mathlib.Data.List.GetD
public import LogicLineages.ComputabilityKnowledge.OracleCertificateTargets
public import LogicLineages.ComputabilityKnowledge.OracleDecoderProof
public import LogicLineages.ComputabilityKnowledge.OracleDerivationProof
public import LogicLineages.ComputabilityKnowledge.OracleProgramProof
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleCertificateProof
open OracleProgram OracleDecoder OracleDerivation OracleCertificate OracleCertificateTargets

private theorem member_le_max (xs : List Nat) (x : Nat) (hx : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact (ih hx).trans (Nat.le_max_right _ _)

theorem certificatePacking : CertificatePacking := by
  intro code input output fuel children
  dsimp only
  have hb : ∀ child ∈ children, child < packNode code input output fuel children := by
    intro child hc
    have h := member_le_max children child hc
    have hh := Nat.left_le_pair (children.foldr max 0 + 1)
      (Nat.pair code (Nat.pair input (Nat.pair output (Nat.pair fuel (Encodable.encode children)))))
    unfold packNode
    omega
  exact ⟨by simp [packNode], by simp [nodeCode, nodeData, packNode],
    by simp [nodeInput, nodeData, packNode], by simp [nodeOutput, nodeData, packNode],
    by simp [nodeFuel, nodeData, packNode], by simp [nodeChildren, nodeData, packNode], hb⟩

@[simp] private theorem nodeCode_pack (code input output fuel : Nat) (children : List Nat) :
    nodeCode (packNode code input output fuel children) = code := by
  simp [nodeCode, nodeData, packNode]

@[simp] private theorem nodeInput_pack (code input output fuel : Nat) (children : List Nat) :
    nodeInput (packNode code input output fuel children) = input := by
  simp [nodeInput, nodeData, packNode]

@[simp] private theorem nodeOutput_pack (code input output fuel : Nat) (children : List Nat) :
    nodeOutput (packNode code input output fuel children) = output := by
  simp [nodeOutput, nodeData, packNode]

@[simp] private theorem nodeFuel_pack (code input output fuel : Nat) (children : List Nat) :
    nodeFuel (packNode code input output fuel children) = fuel := by
  simp [nodeFuel, nodeData, packNode]

@[simp] private theorem nodeChildren_pack (code input output fuel : Nat) (children : List Nat) :
    nodeChildren (packNode code input output fuel children) = some children := by
  simp [nodeChildren, nodeData, packNode]

private theorem table_length (g : Nat → Nat) (n : Nat) : (certificateTable g n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [certificateTable, ih]

private theorem table_get (g : Nat → Nat) (n i : Nat) (hi : i < n) :
    (certificateTable g n).getD i false = validCertificate g i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i < n
      · rw [certificateTable, List.getD_append _ _ _ _ (by simpa [table_length] using h)]
        exact ih h
      · have he : i = n := by omega
        subst i
        rfl

private theorem valid_step (g : Nat → Nat) (i : Nat) :
    validCertificate g i = certificateStep (g (nodeInput i)) i (certificateTable g i) := by
  unfold validCertificate
  rw [certificateTable, List.getD_append_right _ _ _ _ (by simp [table_length])]
  simp [table_length]

private theorem step_iff (g : Nat → Nat) (i : Nat) :
    validCertificate g i = true ↔ ∃ children,
      nodeChildren i = some children ∧ 0 < i ∧ validIndex (nodeCode i) = true ∧
      (∀ child ∈ children, child < i ∧ validCertificate g child = true) ∧
      ruleCheck (g (nodeInput i)) i children = true := by
  rw [valid_step]
  unfold certificateStep
  cases hc : nodeChildren i with
  | none => simp
  | some children =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, hc, Option.some.injEq,
        exists_eq_left']
      constructor
      · rintro ⟨⟨⟨hpos, hv⟩, hall⟩, hr⟩
        exact ⟨hpos, hv, fun child hchild => ⟨(hall child hchild).1,
          by rw [← table_get g i child (hall child hchild).1]; exact (hall child hchild).2⟩, hr⟩
      · rintro ⟨hpos, hv, hall, hr⟩
        exact ⟨⟨⟨hpos, hv⟩, fun child hchild => ⟨(hall child hchild).1,
          by rw [table_get g i child (hall child hchild).1]; exact (hall child hchild).2⟩⟩, hr⟩

private theorem getD_mem (xs : List Nat) (j : Nat) (hj : j < xs.length) : xs.getD j 0 ∈ xs := by
  rw [List.getD_eq_getElem xs 0 hj]
  exact List.getElem_mem hj

theorem numericCertificateSound : NumericCertificateSound := by
  intro g i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hv
      obtain ⟨children, hc, hpos, hvalid, hall, hr⟩ := (step_iff g i).mp hv
      obtain ⟨p, hp⟩ : ∃ p, decode (nodeCode i) = some p := by
        unfold validIndex at hvalid
        cases hd : decode (nodeCode i) with
        | none => simp [hd] at hvalid
        | some p => exact ⟨p, rfl⟩
      have he := OracleDecoderProof.oracleDecoderSound _ _ hp
      refine ⟨p, he, ?_⟩
      have H : ∀ j, j < children.length → ∀ p input,
          childMatches (children.getD j 0) (encode p) input = true →
          Derives g p input (nodeOutput (children.getD j 0)) := by
        intro j hj p input hm
        have hchild := hall _ (getD_mem children j hj)
        obtain ⟨q, hq, hd⟩ := ih _ hchild.1 hchild.2
        simp only [childMatches, Bool.and_eq_true, beq_iff_eq] at hm
        have hqp : q = p := OracleProgramProof.injectiveProgramEncoding (hq.trans hm.1)
        subst q
        simpa only [hm.2] using hd
      cases p with
      | base c =>
          simp [ruleCheck, ← he, encode, tagged] at hr
          exact .base c _ _ (nodeFuel i) hr.2
      | query =>
          simp [ruleCheck, ← he, encode, tagged] at hr
          rw [hr.2]
          exact .query _
      | pair p q =>
          simp only [ruleCheck, ← he, encode, tagged, Nat.add_sub_cancel, Nat.unpair_pair,
            Bool.and_eq_true, beq_iff_eq] at hr
          rw [hr.2]
          exact .pair (H 0 (by omega) p _ hr.1.1.2) (H 1 (by omega) q _ hr.1.2)
      | comp p q =>
          simp only [ruleCheck, ← he, encode, tagged, Nat.add_sub_cancel, Nat.unpair_pair,
            Bool.and_eq_true, beq_iff_eq] at hr
          rw [hr.2]
          exact .comp (H 0 (by omega) q _ hr.1.1.2) (H 1 (by omega) p _ hr.1.2)
      | prec p q =>
          by_cases hn : (nodeInput i).unpair.2 = 0
          · simp only [ruleCheck, ← he, encode, tagged, Nat.add_sub_cancel, Nat.unpair_pair,
              hn, if_pos, Bool.and_eq_true, beq_iff_eq] at hr
            have hi : nodeInput i = Nat.pair (nodeInput i).unpair.1 0 := by
              rw [← hn, Nat.pair_unpair]
            rw [hr.2, hi]
            exact .precZero (H 0 (by omega) p _ hr.1.2)
          · simp only [ruleCheck, ← he, encode, tagged, Nat.add_sub_cancel, Nat.unpair_pair,
              hn, if_false, Bool.and_eq_true, beq_iff_eq] at hr
            have hi : nodeInput i = Nat.pair (nodeInput i).unpair.1 ((nodeInput i).unpair.2 - 1 + 1) := by
              rw [Nat.sub_add_cancel (by omega), Nat.pair_unpair]
            have hprev := H 0 (by omega) (.prec p q) _ hr.1.1.2
            have hnext := H 1 (by omega) q _ hr.1.2
            rw [hr.2, hi]
            exact .precSucc hprev hnext
      | mu p =>
          simp only [ruleCheck, ← he, encode, tagged, Nat.add_sub_cancel, Nat.unpair_pair,
            Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hr
          let prior := List.ofFn (fun j : Fin (nodeOutput i) => nodeOutput (children.getD j 0))
          have hlen : prior.length = nodeOutput i := List.length_ofFn
          have hget : ∀ j (hj : j < nodeOutput i), prior.getD j 0 = nodeOutput (children.getD j 0) := by
            intro j hj
            simp only [prior, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj, Option.getD_some]
          have hd : Derives g (.mu p) (nodeInput i) prior.length := by
            apply Derives.mu prior
            · intro j hj
              have hj' : j < nodeOutput i := by simpa [hlen] using hj
              rw [hget j hj']
              exact H j (by omega) p _ (hr.2 j (by omega)).1
            · intro j hj
              have hj' : j < nodeOutput i := by simpa [hlen] using hj
              rw [hget j hj']
              have hz := (hr.2 j (by omega)).2
              simpa [show j ≠ nodeOutput i by omega] using hz
            · rw [hlen]
              have hz := (hr.2 (nodeOutput i) (by omega)).2
              have hzero : nodeOutput (children.getD (nodeOutput i) 0) = 0 := by simpa using hz
              rw [← hzero]
              exact H (nodeOutput i) (by omega) p _ (hr.2 (nodeOutput i) (by omega)).1
          simpa only [hlen] using hd

private theorem make_certificate (g : Nat → Nat) (p : Program) (input output fuel : Nat)
    (children : List Nat) (hc : ∀ child ∈ children, validCertificate g child = true)
    (hr : ruleCheck (g input) (packNode (encode p) input output fuel children) children = true) :
    ∃ i, validCertificate g i = true ∧ nodeCode i = encode p ∧ nodeInput i = input ∧ nodeOutput i = output := by
  have hp := certificatePacking (encode p) input output fuel children
  refine ⟨packNode (encode p) input output fuel children, ?_, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  apply (step_iff _ _).mpr
  exact ⟨children, hp.2.2.2.2.2.1, hp.1,
    by rw [hp.2.1]; simp [validIndex, OracleDecoderProof.oracleDecoderComplete p],
    fun child hchild => ⟨hp.2.2.2.2.2.2 child hchild, hc child hchild⟩,
    by rw [hp.2.2.1]; exact hr⟩

theorem numericCertificateComplete : NumericCertificateComplete := by
  classical
  intro g p input output hd
  induction hd with
  | base c input output fuel halts =>
      apply make_certificate g (.base c) input output fuel [] (by simp)
      simpa [ruleCheck, encode, tagged] using halts
  | query input =>
      apply make_certificate g .query input (g input) 0 [] (by simp)
      simp [ruleCheck, encode, tagged]
  | pair hp hq ihp ihq =>
      obtain ⟨left, hl, hlc, hli, hlo⟩ := ihp
      obtain ⟨right, hr, hrc, hri, hro⟩ := ihq
      apply make_certificate g (.pair _ _) _ _ 0 [left, right]
      · intro child hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with he | he
        · rw [he]; exact hl
        · rw [he]; exact hr
      · simp [ruleCheck, encode, tagged,
          childMatches, hlc, hli, hlo, hrc, hri, hro]
  | comp hq hp ihq ihp =>
      obtain ⟨left, hl, hlc, hli, hlo⟩ := ihq
      obtain ⟨right, hr, hrc, hri, hro⟩ := ihp
      apply make_certificate g (.comp _ _) _ _ 0 [left, right]
      · intro child hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with he | he
        · rw [he]; exact hl
        · rw [he]; exact hr
      · simp [ruleCheck, encode, tagged,
          childMatches, hlc, hli, hlo, hrc, hri, hro]
  | precZero hp ih =>
      obtain ⟨child, hc, hcc, hci, hco⟩ := ih
      apply make_certificate g (.prec _ _) _ _ 0 [child]
      · simpa using hc
      · simp [ruleCheck, encode, tagged,
          childMatches, hcc, hci, hco]
  | precSucc hprev hstep ihprev ihstep =>
      obtain ⟨left, hl, hlc, hli, hlo⟩ := ihprev
      obtain ⟨right, hr, hrc, hri, hro⟩ := ihstep
      apply make_certificate g (.prec _ _) _ _ 0 [left, right]
      · intro child hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with he | he
        · rw [he]; exact hl
        · rw [he]; exact hr
      · simp [ruleCheck, encode, tagged,
          childMatches, hlc, hli, hlo, hrc, hri, hro]
  | @mu p parameter prior runs nonzero last ihRuns ihLast =>
      have H : ∀ j : Fin prior.length, ∃ i, validCertificate g i = true ∧ nodeCode i = encode p ∧
          nodeInput i = Nat.pair parameter j ∧ nodeOutput i = prior.getD j 0 := by
        intro j
        exact ihRuns j j.isLt
      choose cert hcert using H
      obtain ⟨lastCert, hl, hlc, hli, hlo⟩ := ihLast
      let initial := List.ofFn cert
      let children := initial ++ [lastCert]
      have hlen : children.length = prior.length + 1 := by simp [children, initial]
      have hget : ∀ j (hj : j < prior.length), children.getD j 0 = cert ⟨j, hj⟩ := by
        intro j hj
        rw [List.getD_append _ _ _ _ (by simpa [initial] using hj)]
        simp only [initial, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj, Option.getD_some]
      have hlast : children.getD prior.length 0 = lastCert := by
        rw [List.getD_append_right _ _ _ _ (by simp [initial])]
        simp [initial]
      apply make_certificate g (.mu p) parameter prior.length 0 children
      · intro child hc
        simp only [children, initial, List.mem_append, List.mem_ofFn, List.mem_singleton] at hc
        rcases hc with ⟨j, rfl⟩ | rfl
        · exact (hcert j).1
        · exact hl
      · simp only [ruleCheck, nodeCode_pack, nodeInput_pack, nodeOutput_pack, encode, tagged,
          Nat.add_sub_cancel, Nat.unpair_pair, hlen, beq_self_eq_true, Bool.true_and,
          List.all_eq_true, List.mem_range]
        intro j hj
        by_cases he : j = prior.length
        · subst j
          rw [hlast]
          simp [childMatches, hlc, hli, hlo]
        · have hj' : j < prior.length := by omega
          rw [hget j hj']
          simp [childMatches, (hcert ⟨j, hj'⟩).2.1, (hcert ⟨j, hj'⟩).2.2.1,
            (hcert ⟨j, hj'⟩).2.2.2, he]
          exact nonzero j hj'

private theorem pr_nodeData : Primrec nodeData :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
private theorem pr_nodeCode : Primrec nodeCode := Primrec.fst.comp (Primrec.unpair.comp pr_nodeData)
private theorem pr_nodeInput : Primrec nodeInput :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData)))
private theorem pr_nodeOutput : Primrec nodeOutput :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData)))))
private theorem pr_nodeFuel : Primrec nodeFuel :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData)))))))
private theorem pr_nodeChildren : Primrec nodeChildren :=
  Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp pr_nodeData))))))))

private theorem pr_all {α β : Type} [Primcodable α] [Primcodable β]
    (l : α → List β) (p : α → β → Bool) (hl : Primrec l) (hp : Primrec₂ p) :
    Primrec (fun a => (l a).all (p a)) := by
  have h := Primrec.list_foldr hl (Primrec.const true)
    (Primrec.to₂ (Primrec.and.comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)))
  apply h.of_eq
  intro a
  induction l a with
  | nil => rfl
  | cons b bs ih => simp [List.all_cons, ih]

private abbrev RuleData := Nat × Nat × List Nat
private theorem pr_muPredicate : Primrec (fun z : RuleData × Nat =>
    childMatches (z.1.2.2.getD z.2 0) (nodeCode z.1.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.1.2.1) z.2) &&
    if z.2 = nodeOutput z.1.2.1 then nodeOutput (z.1.2.2.getD z.2 0) == 0 else !(nodeOutput (z.1.2.2.getD z.2 0) == 0)) := by
  have h1 : Primrec (fun z : RuleData × Nat => Prod.fst (z)) := Primrec.fst.comp Primrec.id
  have h2 : Primrec (fun z : RuleData × Nat => Prod.snd (z)) := Primrec.snd.comp Primrec.id
  have h3 : Primrec (fun z : RuleData × Nat => Prod.snd (Prod.fst (z))) := Primrec.snd.comp h1
  have h4 : Primrec (fun z : RuleData × Nat => Prod.fst (Prod.snd (Prod.fst (z)))) := Primrec.fst.comp h3
  have h5 : Primrec (fun z : RuleData × Nat => Prod.snd (Prod.fst (z))) := Primrec.snd.comp h1
  have h6 : Primrec (fun z : RuleData × Nat => Prod.snd (Prod.snd (Prod.fst (z)))) := Primrec.snd.comp h5
  have h7 : Primrec (fun z : RuleData × Nat => nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) := pr_nodeCode.comp h4
  have h8 : Primrec (fun z : RuleData × Nat => nodeInput (Prod.fst (Prod.snd (Prod.fst (z))))) := pr_nodeInput.comp h4
  have h9 : Primrec (fun z : RuleData × Nat => nodeOutput (Prod.fst (Prod.snd (Prod.fst (z))))) := pr_nodeOutput.comp h4
  have h10 : Primrec (fun z : RuleData × Nat => Nat.sub (nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) (1)) := Primrec.nat_sub.comp h7 (Primrec.const 1)
  have h11 : Primrec (fun z : RuleData × Nat => Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) (1))) := Primrec.unpair.comp h10
  have h12 : Primrec (fun z : RuleData × Nat => Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) (1)))) := Primrec.snd.comp h11
  have h13 : Primrec (fun z : RuleData × Nat => (fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z))) := (Primrec.list_getD 0).comp h6 h2
  have h14 : Primrec (fun z : RuleData × Nat => Nat.pair (nodeInput (Prod.fst (Prod.snd (Prod.fst (z))))) (Prod.snd (z))) := Primrec₂.natPair.comp h8 h2
  have h15 : Primrec (fun z : RuleData × Nat => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) := pr_nodeCode.comp h13
  have h16 : Primrec (fun z : RuleData × Nat => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) (1))))) := Primrec.beq.comp h15 h12
  have h17 : Primrec (fun z : RuleData × Nat => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) := pr_nodeInput.comp h13
  have h18 : Primrec (fun z : RuleData × Nat => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (Nat.pair (nodeInput (Prod.fst (Prod.snd (Prod.fst (z))))) (Prod.snd (z)))) := Primrec.beq.comp h17 h14
  have h19 : Primrec (fun z : RuleData × Nat => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) (1))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (Nat.pair (nodeInput (Prod.fst (Prod.snd (Prod.fst (z))))) (Prod.snd (z))))) := Primrec.and.comp h16 h18
  have h20 : Primrec (fun z : RuleData × Nat => nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) := pr_nodeOutput.comp h13
  have h21 : Primrec (fun z : RuleData × Nat => BEq.beq (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (0)) := Primrec.beq.comp h20 (Primrec.const 0)
  have h22 : Primrec (fun z : RuleData × Nat => Bool.not (BEq.beq (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (0))) := Primrec.not.comp h21
  have h23 : Primrec (fun z : RuleData × Nat => if Prod.snd (z) = nodeOutput (Prod.fst (Prod.snd (Prod.fst (z)))) then BEq.beq (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (0) else Bool.not (BEq.beq (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (0))) := Primrec.ite (Primrec.eq.comp h2 h9) h21 h22
  have h24 : Primrec (fun z : RuleData × Nat => Bool.and (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (Prod.fst (z))))) (1))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (Nat.pair (nodeInput (Prod.fst (Prod.snd (Prod.fst (z))))) (Prod.snd (z))))) (if Prod.snd (z) = nodeOutput (Prod.fst (Prod.snd (Prod.fst (z)))) then BEq.beq (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (0) else Bool.not (BEq.beq (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (Prod.fst (z)))) (Prod.snd (z)))) (0)))) := Primrec.and.comp h19 h23
  exact h24

private theorem pr_rule_h1 : Primrec (fun z : RuleData => Prod.fst (z)) := Primrec.fst.comp Primrec.id

private theorem pr_rule_h2 : Primrec (fun z : RuleData => Prod.snd (z)) := Primrec.snd.comp Primrec.id

private theorem pr_rule_h3 : Primrec (fun z : RuleData => Prod.fst (Prod.snd (z))) := Primrec.fst.comp pr_rule_h2

private theorem pr_rule_h4 : Primrec (fun z : RuleData => Prod.snd (z)) := Primrec.snd.comp Primrec.id

private theorem pr_rule_h5 : Primrec (fun z : RuleData => Prod.snd (Prod.snd (z))) := Primrec.snd.comp pr_rule_h4

private theorem pr_rule_h6 : Primrec (fun z : RuleData => nodeCode (Prod.fst (Prod.snd (z)))) := pr_nodeCode.comp pr_rule_h3

private theorem pr_rule_h7 : Primrec (fun z : RuleData => nodeInput (Prod.fst (Prod.snd (z)))) := pr_nodeInput.comp pr_rule_h3

private theorem pr_rule_h8 : Primrec (fun z : RuleData => nodeOutput (Prod.fst (Prod.snd (z)))) := pr_nodeOutput.comp pr_rule_h3

private theorem pr_rule_h9 : Primrec (fun z : RuleData => nodeFuel (Prod.fst (Prod.snd (z)))) := pr_nodeFuel.comp pr_rule_h3

private theorem pr_rule_h10 : Primrec (fun z : RuleData => Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1)) := Primrec.nat_sub.comp pr_rule_h6 (Primrec.const 1)

private theorem pr_rule_h11 : Primrec (fun z : RuleData => Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) := Primrec.unpair.comp pr_rule_h10

private theorem pr_rule_h12 : Primrec (fun z : RuleData => Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1)))) := Primrec.fst.comp pr_rule_h11

private theorem pr_rule_h13 : Primrec (fun z : RuleData => Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1)))) := Primrec.snd.comp pr_rule_h11

private theorem pr_rule_h14 : Primrec (fun z : RuleData => Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) := Primrec.unpair.comp pr_rule_h13

private theorem pr_rule_h15 : Primrec (fun z : RuleData => Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1)))))) := Primrec.fst.comp pr_rule_h14

private theorem pr_rule_h16 : Primrec (fun z : RuleData => Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) := Primrec.unpair.comp pr_rule_h13

private theorem pr_rule_h17 : Primrec (fun z : RuleData => Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1)))))) := Primrec.snd.comp pr_rule_h16

private theorem pr_rule_h18 : Primrec (fun z : RuleData => (fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)) := (Primrec.list_getD 0).comp pr_rule_h5 (Primrec.const 0)

private theorem pr_rule_h19 : Primrec (fun z : RuleData => (fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)) := (Primrec.list_getD 0).comp pr_rule_h5 (Primrec.const 1)

private theorem pr_rule_h20 : Primrec (fun z : RuleData => nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeOutput.comp pr_rule_h18

private theorem pr_rule_h21 : Primrec (fun z : RuleData => nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeOutput.comp pr_rule_h19

private theorem pr_rule_h22 : Primrec (fun z : RuleData => List.length (Prod.snd (Prod.snd (z)))) := Primrec.list_length.comp pr_rule_h5

private theorem pr_rule_h23 : Primrec (fun z : RuleData => BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (0)) := Primrec.beq.comp pr_rule_h22 (Primrec.const 0)

private theorem pr_rule_h24 : Primrec (fun z : RuleData => BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) := Primrec.beq.comp pr_rule_h22 (Primrec.const 1)

private theorem pr_rule_h25 : Primrec (fun z : RuleData => BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) := Primrec.beq.comp pr_rule_h22 (Primrec.const 2)

private theorem pr_rule_h26 : Primrec (fun z : RuleData => (Denumerable.ofNat Nat.Partrec.Code) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) := (Primrec.ofNat Nat.Partrec.Code).comp pr_rule_h13

private theorem pr_rule_hEval : Primrec (fun z : RuleData => Nat.Partrec.Code.evaln (nodeFuel (Prod.fst (Prod.snd (z)))) ((Denumerable.ofNat Nat.Partrec.Code) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) (nodeInput (Prod.fst (Prod.snd (z))))) := by
  have h := Nat.Partrec.Code.primrec_evaln.comp ((pr_rule_h9.pair pr_rule_h26).pair pr_rule_h7)
  apply h.of_eq
  intro z
  dsimp only

private theorem pr_rule_h27 : Primrec (fun z : RuleData => Option.some (nodeOutput (Prod.fst (Prod.snd (z))))) := Primrec.option_some.comp pr_rule_h8

private theorem pr_rule_h28 : Primrec (fun z : RuleData => BEq.beq (Nat.Partrec.Code.evaln (nodeFuel (Prod.fst (Prod.snd (z)))) ((Denumerable.ofNat Nat.Partrec.Code) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) (nodeInput (Prod.fst (Prod.snd (z))))) (Option.some (nodeOutput (Prod.fst (Prod.snd (z)))))) := by
  have h := (Primrec.eq.comp pr_rule_hEval pr_rule_h27).decide
  apply h.of_eq
  intro z
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]

private theorem pr_rule_h29 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (0)) (BEq.beq (Nat.Partrec.Code.evaln (nodeFuel (Prod.fst (Prod.snd (z)))) ((Denumerable.ofNat Nat.Partrec.Code) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) (nodeInput (Prod.fst (Prod.snd (z))))) (Option.some (nodeOutput (Prod.fst (Prod.snd (z))))))) := Primrec.and.comp pr_rule_h23 pr_rule_h28

private theorem pr_rule_h30 : Primrec (fun z : RuleData => BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Prod.fst (z))) := Primrec.beq.comp pr_rule_h8 pr_rule_h1

private theorem pr_rule_h31 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (0)) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Prod.fst (z)))) := Primrec.and.comp pr_rule_h23 pr_rule_h30

private theorem pr_rule_h32 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeCode.comp pr_rule_h18

private theorem pr_rule_h33 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) := Primrec.beq.comp pr_rule_h32 pr_rule_h15

private theorem pr_rule_h34 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeInput.comp pr_rule_h18

private theorem pr_rule_h35 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))) := Primrec.beq.comp pr_rule_h34 pr_rule_h7

private theorem pr_rule_h36 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z)))))) := Primrec.and.comp pr_rule_h33 pr_rule_h35

private theorem pr_rule_h37 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) := Primrec.and.comp pr_rule_h25 pr_rule_h36

private theorem pr_rule_h38 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeCode.comp pr_rule_h19

private theorem pr_rule_h39 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) := Primrec.beq.comp pr_rule_h38 pr_rule_h17

private theorem pr_rule_h40 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeInput.comp pr_rule_h19

private theorem pr_rule_h41 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z))))) := Primrec.beq.comp pr_rule_h40 pr_rule_h7

private theorem pr_rule_h42 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z)))))) := Primrec.and.comp pr_rule_h39 pr_rule_h41

private theorem pr_rule_h43 : Primrec (fun z : RuleData => Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z))))))) := Primrec.and.comp pr_rule_h37 pr_rule_h42

private theorem pr_rule_h44 : Primrec (fun z : RuleData => Nat.pair (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) := Primrec₂.natPair.comp pr_rule_h20 pr_rule_h21

private theorem pr_rule_h45 : Primrec (fun z : RuleData => BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Nat.pair (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) := Primrec.beq.comp pr_rule_h8 pr_rule_h44

private theorem pr_rule_h46 : Primrec (fun z : RuleData => Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Nat.pair (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))))) := Primrec.and.comp pr_rule_h43 pr_rule_h45

private theorem pr_rule_h47 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeCode.comp pr_rule_h18

private theorem pr_rule_h48 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) := Primrec.beq.comp pr_rule_h47 pr_rule_h17

private theorem pr_rule_h49 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeInput.comp pr_rule_h18

private theorem pr_rule_h50 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))) := Primrec.beq.comp pr_rule_h49 pr_rule_h7

private theorem pr_rule_h51 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z)))))) := Primrec.and.comp pr_rule_h48 pr_rule_h50

private theorem pr_rule_h52 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) := Primrec.and.comp pr_rule_h25 pr_rule_h51

private theorem pr_rule_h53 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeCode.comp pr_rule_h19

private theorem pr_rule_h54 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) := Primrec.beq.comp pr_rule_h53 pr_rule_h15

private theorem pr_rule_h55 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeInput.comp pr_rule_h19

private theorem pr_rule_h56 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) := Primrec.beq.comp pr_rule_h55 pr_rule_h20

private theorem pr_rule_h57 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))))) := Primrec.and.comp pr_rule_h54 pr_rule_h56

private theorem pr_rule_h58 : Primrec (fun z : RuleData => Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) := Primrec.and.comp pr_rule_h52 pr_rule_h57

private theorem pr_rule_h59 : Primrec (fun z : RuleData => BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) := Primrec.beq.comp pr_rule_h8 pr_rule_h21

private theorem pr_rule_h60 : Primrec (fun z : RuleData => Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) := Primrec.and.comp pr_rule_h58 pr_rule_h59

private theorem pr_rule_h61 : Primrec (fun z : RuleData => Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) := Primrec.unpair.comp pr_rule_h7

private theorem pr_rule_h62 : Primrec (fun z : RuleData => Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) := Primrec.fst.comp pr_rule_h61

private theorem pr_rule_h63 : Primrec (fun z : RuleData => Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) := Primrec.unpair.comp pr_rule_h7

private theorem pr_rule_h64 : Primrec (fun z : RuleData => Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) := Primrec.snd.comp pr_rule_h63

private theorem pr_rule_h65 : Primrec (fun z : RuleData => Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) := Primrec.nat_sub.comp pr_rule_h64 (Primrec.const 1)

private theorem pr_rule_h66 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeCode.comp pr_rule_h18

private theorem pr_rule_h67 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) := Primrec.beq.comp pr_rule_h66 pr_rule_h15

private theorem pr_rule_h68 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeInput.comp pr_rule_h18

private theorem pr_rule_h69 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))) := Primrec.beq.comp pr_rule_h68 pr_rule_h62

private theorem pr_rule_h70 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))))) := Primrec.and.comp pr_rule_h67 pr_rule_h69

private theorem pr_rule_h71 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) := Primrec.and.comp pr_rule_h24 pr_rule_h70

private theorem pr_rule_h72 : Primrec (fun z : RuleData => BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) := Primrec.beq.comp pr_rule_h8 pr_rule_h20

private theorem pr_rule_h73 : Primrec (fun z : RuleData => Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))))) := Primrec.and.comp pr_rule_h71 pr_rule_h72

private theorem pr_rule_h74 : Primrec (fun z : RuleData => Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1))) := Primrec₂.natPair.comp pr_rule_h62 pr_rule_h65

private theorem pr_rule_h75 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeCode.comp pr_rule_h18

private theorem pr_rule_h76 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) := Primrec.beq.comp pr_rule_h75 pr_rule_h6

private theorem pr_rule_h77 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) := pr_nodeInput.comp pr_rule_h18

private theorem pr_rule_h78 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))) := Primrec.beq.comp pr_rule_h77 pr_rule_h74

private theorem pr_rule_h79 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1))))) := Primrec.and.comp pr_rule_h76 pr_rule_h78

private theorem pr_rule_h80 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) := Primrec.and.comp pr_rule_h25 pr_rule_h79

private theorem pr_rule_h81 : Primrec (fun z : RuleData => Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) := Primrec₂.natPair.comp pr_rule_h65 pr_rule_h20

private theorem pr_rule_h82 : Primrec (fun z : RuleData => Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))))) := Primrec₂.natPair.comp pr_rule_h62 pr_rule_h81

private theorem pr_rule_h83 : Primrec (fun z : RuleData => nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeCode.comp pr_rule_h19

private theorem pr_rule_h84 : Primrec (fun z : RuleData => BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) := Primrec.beq.comp pr_rule_h83 pr_rule_h17

private theorem pr_rule_h85 : Primrec (fun z : RuleData => nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) := pr_nodeInput.comp pr_rule_h19

private theorem pr_rule_h86 : Primrec (fun z : RuleData => BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) := Primrec.beq.comp pr_rule_h85 pr_rule_h82

private theorem pr_rule_h87 : Primrec (fun z : RuleData => Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))))))) := Primrec.and.comp pr_rule_h84 pr_rule_h86

private theorem pr_rule_h88 : Primrec (fun z : RuleData => Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) := Primrec.and.comp pr_rule_h80 pr_rule_h87

private theorem pr_rule_h89 : Primrec (fun z : RuleData => BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) := Primrec.beq.comp pr_rule_h8 pr_rule_h21

private theorem pr_rule_h90 : Primrec (fun z : RuleData => Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) := Primrec.and.comp pr_rule_h88 pr_rule_h89

private theorem pr_rule_h91 : Primrec (fun z : RuleData => if Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) = 0 then Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) else Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) := Primrec.ite (Primrec.eq.comp pr_rule_h64 (Primrec.const 0)) pr_rule_h73 pr_rule_h90

private theorem pr_rule_hMuAll : Primrec (fun z : RuleData =>
    (List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) :=
  pr_all (fun z : RuleData => List.range (List.length (Prod.snd (Prod.snd (z))))) _ (Primrec.list_range.comp pr_rule_h22) pr_muPredicate.to₂

private theorem pr_rule_h92 : Primrec (fun z : RuleData => Nat.succ (nodeOutput (Prod.fst (Prod.snd (z))))) := Primrec.succ.comp pr_rule_h8

private theorem pr_rule_h93 : Primrec (fun z : RuleData => BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) := Primrec.beq.comp pr_rule_h22 pr_rule_h92

private theorem pr_rule_h94 : Primrec (fun z : RuleData => Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0)))) := Primrec.and.comp pr_rule_h93 pr_rule_hMuAll

private theorem pr_rule_h95 : Primrec (fun z : RuleData => if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 5 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) else false) := Primrec.ite (Primrec.eq.comp pr_rule_h12 (Primrec.const 5)) pr_rule_h94 (Primrec.const false)

private theorem pr_rule_h96 : Primrec (fun z : RuleData => if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 4 then if Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) = 0 then Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) else Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 5 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) else false) := Primrec.ite (Primrec.eq.comp pr_rule_h12 (Primrec.const 4)) pr_rule_h91 pr_rule_h95

private theorem pr_rule_h97 : Primrec (fun z : RuleData => if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 3 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 4 then if Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) = 0 then Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) else Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 5 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) else false) := Primrec.ite (Primrec.eq.comp pr_rule_h12 (Primrec.const 3)) pr_rule_h60 pr_rule_h96

private theorem pr_rule_h98 : Primrec (fun z : RuleData => if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 2 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Nat.pair (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 3 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 4 then if Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) = 0 then Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) else Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 5 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) else false) := Primrec.ite (Primrec.eq.comp pr_rule_h12 (Primrec.const 2)) pr_rule_h46 pr_rule_h97

private theorem pr_rule_h99 : Primrec (fun z : RuleData => if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 1 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (0)) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Prod.fst (z))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 2 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Nat.pair (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 3 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 4 then if Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) = 0 then Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) else Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 5 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) else false) := Primrec.ite (Primrec.eq.comp pr_rule_h12 (Primrec.const 1)) pr_rule_h31 pr_rule_h98

private theorem pr_rule_h100 : Primrec (fun z : RuleData => if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 0 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (0)) (BEq.beq (Nat.Partrec.Code.evaln (nodeFuel (Prod.fst (Prod.snd (z)))) ((Denumerable.ofNat Nat.Partrec.Code) (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))) (nodeInput (Prod.fst (Prod.snd (z))))) (Option.some (nodeOutput (Prod.fst (Prod.snd (z)))))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 1 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (0)) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Prod.fst (z))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 2 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeInput (Prod.fst (Prod.snd (z))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (Nat.pair (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 3 then Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeInput (Prod.fst (Prod.snd (z))))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 4 then if Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))) = 0 then Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (1)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z))))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))) else Bool.and (Bool.and (Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (2)) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (nodeCode (Prod.fst (Prod.snd (z))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)))))) (Bool.and (BEq.beq (nodeCode ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Prod.snd (Nat.unpair (Prod.snd (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))))))) (BEq.beq (nodeInput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1))) (Nat.pair (Prod.fst (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (Nat.pair (Nat.sub (Prod.snd (Nat.unpair (nodeInput (Prod.fst (Prod.snd (z)))))) (1)) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (0)))))))) (BEq.beq (nodeOutput (Prod.fst (Prod.snd (z)))) (nodeOutput ((fun l n => l.getD n 0) (Prod.snd (Prod.snd (z))) (1)))) else if Prod.fst (Nat.unpair (Nat.sub (nodeCode (Prod.fst (Prod.snd (z)))) (1))) = 5 then Bool.and (BEq.beq (List.length (Prod.snd (Prod.snd (z)))) (Nat.succ (nodeOutput (Prod.fst (Prod.snd (z)))))) ((List.range z.2.2.length).all (fun j => childMatches (z.2.2.getD j 0) (nodeCode z.2.1 - 1).unpair.2 (Nat.pair (nodeInput z.2.1) j) && if j = nodeOutput z.2.1 then nodeOutput (z.2.2.getD j 0) == 0 else !(nodeOutput (z.2.2.getD j 0) == 0))) else false) := Primrec.ite (Primrec.eq.comp pr_rule_h12 (Primrec.const 0)) pr_rule_h29 pr_rule_h99

private theorem isempty_bool (xs : List Nat) : (xs.length == 0) = xs.isEmpty := by
  cases xs <;> simp

private theorem pr_ruleCheck : Primrec (fun z : RuleData => ruleCheck z.1 z.2.1 z.2.2) := by
  apply pr_rule_h100.of_eq
  intro z
  rcases ht : (nodeCode z.2.1 - 1).unpair.1 with (_ | _ | _ | _ | _ | _ | t) <;>
    simp [ruleCheck, ht, childMatches, isempty_bool]

private abbrev StepData := Nat × Nat × List Bool
private theorem pr_childCheck : Primrec (fun z : (StepData × List Nat) × Nat =>
    decide (z.2 < z.1.1.2.1) && z.1.1.2.2.getD z.2 false) := by
  exact Primrec.and.comp
    (Primrec.nat_lt.comp Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).decide
    ((Primrec.list_getD false).comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)

theorem primitiveRecursiveCertificateStep : PrimitiveRecursiveCertificateStep := by
  have hi : Primrec (fun z : StepData × List Nat => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun z : StepData × List Nat => z.1.1) := Primrec.fst.comp Primrec.fst
  have hv := OracleDecoderProof.primitiveRecursiveValidity.comp (pr_nodeCode.comp hi)
  have hc := pr_all (fun z : StepData × List Nat => z.2) _ Primrec.snd pr_childCheck.to₂
  have hr := pr_ruleCheck.comp (ha.pair (hi.pair Primrec.snd))
  have hbody := Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp (Primrec.nat_lt.comp (Primrec.const 0) hi).decide hv) hc) hr
  apply (Primrec.option_casesOn
    (pr_nodeChildren.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const false) hbody.to₂).of_eq
  intro z
  unfold certificateStep
  cases nodeChildren z.2.1 <;> rfl

private def updateEncoded (z : Nat) : Nat :=
  Encodable.encode (((Encodable.decode (α := List Bool) z.unpair.2.unpair.2).getD []) ++
    [certificateStep z.unpair.1 z.unpair.2.unpair.1
      ((Encodable.decode (α := List Bool) z.unpair.2.unpair.2).getD [])])

private theorem pr_updateEncoded : Primrec updateEncoded := by
  have ha : Primrec (fun z : Nat => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hi : Primrec (fun z : Nat => z.unpair.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hv : Primrec (fun z : Nat => z.unpair.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hl := Primrec.option_getD.comp (Primrec.decode.comp hv) (Primrec.const ([] : List Bool))
  have hstep := primitiveRecursiveCertificateStep.comp (ha.pair (hi.pair hl))
  have hlist := Primrec.list_concat.comp hl hstep
  have h := Primrec.encode.comp hlist
  exact h.of_eq (fun _ => rfl)

theorem relativeCertificateVerifier : RelativeCertificateVerifier := by
  intro g
  let O : Set (Nat → Part Nat) := {fun n => Part.some (g n)}
  have hg : ComputableIn O g := RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.oracle _ (by exact rfl))
  have hj : ComputableIn O (fun z : Nat => z.unpair.2.unpair.1) :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).computableIn
  have hv : ComputableIn O (fun z : Nat => z.unpair.2.unpair.2) :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).computableIn
  have harg := OracleRelativeRecursionProof.relativeComposition O _ _ pr_nodeInput.computableIn hj
  have hanswer := OracleRelativeRecursionProof.relativeComposition O _ _ hg harg
  have hpair := OracleRelativeRecursionProof.relativeNumericPairing O _ _ hj hv
  have hargs := OracleRelativeRecursionProof.relativeNumericPairing O _ _ hanswer hpair
  have hstep := OracleRelativeRecursionProof.relativeComposition O _ _ pr_updateEncoded.computableIn hargs
  let step : Nat → Nat := fun z => updateEncoded (Nat.pair (g (nodeInput z.unpair.2.unpair.1))
    (Nat.pair z.unpair.2.unpair.1 z.unpair.2.unpair.2))
  have hs : ComputableIn O step := hstep
  have ht := OracleRelativeRecursionProof.relativePrimitiveRecursion O
    (fun _ => Encodable.encode ([] : List Bool)) step (Primrec.const _).computableIn hs
  have he : ∀ a n, OracleRelativeRecursion.parameterRec (fun _ => Encodable.encode ([] : List Bool)) step
      (Nat.pair a n) = Encodable.encode (certificateTable g n) := by
    intro a n
    simp only [OracleRelativeRecursion.parameterRec, Nat.unpair_pair]
    induction n with
    | zero => rfl
    | succ n ih =>
        change step (Nat.pair a (Nat.pair n (Nat.rec (Encodable.encode ([] : List Bool))
          (fun j previous => step (Nat.pair a (Nat.pair j previous))) n))) = _
        rw [ih]
        simp only [step, updateEncoded, Nat.unpair_pair, Encodable.encodek, Option.getD_some, certificateTable]
  have hin : ComputableIn O (fun n => Nat.pair 0 (n + 1)) :=
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.succ).computableIn
  have htable := OracleRelativeRecursionProof.relativeComposition O _ _ ht hin
  have hp := OracleRelativeRecursionProof.relativeNumericPairing O _ _ htable (Primrec.id.computableIn)
  have hlookup : Primrec (fun z : Nat => if
      ((Encodable.decode (α := List Bool) z.unpair.1).getD []).getD z.unpair.2 false then 1 else 0) := by
    apply (Primrec.cond ((Primrec.list_getD false).comp
      (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const []))
      (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1) (Primrec.const 0)).of_eq
    intro z
    cases ((Encodable.decode (α := List Bool) z.unpair.1).getD []).getD z.unpair.2 false <;> rfl
  have hres := OracleRelativeRecursionProof.relativeComposition O _ _ hlookup.computableIn hp
  apply hres.of_eq
  intro n
  simp only [Nat.unpair_pair, he, Encodable.encodek, Option.getD_some]
  rfl

end LogicLineages.ComputabilityKnowledge.OracleCertificateProof
