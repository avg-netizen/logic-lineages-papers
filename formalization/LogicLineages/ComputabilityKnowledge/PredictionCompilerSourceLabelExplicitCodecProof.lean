module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodecTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodec
open Turing.PartrecToTM2 PredictionCompilerFinitePayloadCodec

private theorem fold_zero {α : Type} (z : α) (step : Nat → Nat → Quint α → α) : fold z step 0 = z := by
  rw [fold]; simp

private theorem fold_node {α : Type} (z : α) (step : Nat → Nat → Quint α → α)
    (tag p : Nat) (cs : Quint Nat) (ht : tag < 8) :
    fold z step (node tag p cs) = step tag p
      (fold z step cs.1, fold z step cs.2.1, fold z step cs.2.2.1,
        fold z step cs.2.2.2.1, fold z step cs.2.2.2.2) := by
  have hn : node tag p cs ≠ 0 := by unfold node; omega
  have hm : (node tag p cs - 1) % 8 = tag := by unfold node; omega
  have hd : (node tag p cs - 1) / 8 = Nat.pair p (pack cs) := by unfold node; omega
  rw [fold]
  simp [hn, hm, hd, pack]

theorem foldCorrect : Targets.FoldCorrect := by
  intro α z step q
  induction q <;> simp_all [code, fold_node, fold_zero, termFold]

private theorem readNat_putNat (α : Type) [i : Primcodable α] [Inhabited α] (x : α) :
    readNat α (putNat x) = x := by
  unfold readNat putNat
  rw [Encodable.encodek]
  rfl

theorem roundtrip : Targets.Roundtrip := by
  intro q
  unfold decode
  rw [foldCorrect]
  induction q with
  | read f ih =>
    simp only [termFold]
    simp [assemble, ih]
    congr 1
    funext s
    cases s with
    | none => rfl
    | some a => cases a <;> rfl
  | _ => simp_all [termFold, assemble, readNat_putNat]

theorem foldPrimitiveRecursive : Targets.FoldPrimitiveRecursive := by
  intro α inst z step hs
  let tag : Nat → Nat := fun n => (n-1)%8
  let payload : Nat → Nat := fun n => ((n-1)/8).unpair.1
  let r : Nat → Nat := fun n => ((n-1)/8).unpair.2
  let children : Nat → List Nat := fun n => if n=0 then [] else
    [ (r n).unpair.1, (r n).unpair.2.unpair.1, (r n).unpair.2.unpair.2.unpair.1,
      (r n).unpair.2.unpair.2.unpair.2.unpair.1, (r n).unpair.2.unpair.2.unpair.2.unpair.2 ]
  let assemble : Nat → List α → Option α := fun n rs => some (if n=0 then z else
    step (tag n) (payload n) (rs.getD 0 z, rs.getD 1 z, rs.getD 2 z, rs.getD 3 z, rs.getD 4 z))
  have ht : Primrec tag := Primrec.nat_mod.comp Primrec.pred (Primrec.const 8)
  have hd : Primrec (fun n : Nat => (n-1)/8) := Primrec.nat_div.comp Primrec.pred (Primrec.const 8)
  have hp : Primrec payload := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr : Primrec r := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hright {β : Type} [Primcodable β] {f : β → Nat} (h : Primrec f) : Primrec (fun x => (f x).unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp h)
  have hleft {β : Type} [Primcodable β] {f : β → Nat} (h : Primrec f) : Primrec (fun x => (f x).unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp h)
  have hc : Primrec children := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const [])
    (Primrec.list_cons.comp (hleft hr) (Primrec.list_cons.comp (hleft (hright hr))
      (Primrec.list_cons.comp (hleft (hright (hright hr)))
        (Primrec.list_cons.comp (hleft (hright (hright (hright hr))))
          (Primrec.list_cons.comp (hright (hright (hright (hright hr)))) (Primrec.const []))))))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : Nat × List α => p.2.getD k z) :=
      (Primrec.list_getD z).comp Primrec.snd (Primrec.const k)
    have hv : Primrec (fun p : Nat × List α =>
        (p.2.getD 0 z, p.2.getD 1 z, p.2.getD 2 z, p.2.getD 3 z, p.2.getD 4 z)) :=
      (hg 0).pair ((hg 1).pair ((hg 2).pair ((hg 3).pair (hg 4))))
    have hh := hs.comp ((ht.comp Primrec.fst).pair ((hp.comp Primrec.fst).pair hv))
    exact (Primrec.option_some.comp (Primrec.ite
      (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const z) hh)).to₂
  apply Primrec.nat_omega_rec' (fold z step) Primrec.id hc ha
  · intro n t hmem
    by_cases h0 : n=0
    · simp [children, h0] at hmem
    have hm : (n-1)/8 < n := (Nat.div_le_self _ _).trans_lt (by omega)
    have h0r : r n < n := (Nat.unpair_right_le _).trans_lt hm
    have h1r := (Nat.unpair_right_le (r n)).trans_lt h0r
    have h2r := (Nat.unpair_right_le (r n).unpair.2).trans_lt h1r
    have h3r := (Nat.unpair_right_le (r n).unpair.2.unpair.2).trans_lt h2r
    simp only [children, if_neg h0, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h
    · rw [h]; exact (Nat.unpair_left_le _).trans_lt h0r
    · rw [h]; exact (Nat.unpair_left_le _).trans_lt h1r
    · rw [h]; exact (Nat.unpair_left_le _).trans_lt h2r
    · rw [h]; exact (Nat.unpair_left_le _).trans_lt h3r
    · rw [h]; exact (Nat.unpair_right_le _).trans_lt h3r
  · intro n
    rw [fold]
    by_cases h0 : n=0 <;> simp [children, assemble, h0, tag, payload, r]

private def qmap {α β : Type} (f : α → β) (t : Quint α) : Quint β :=
  (f t.1, f t.2.1, f t.2.2.1, f t.2.2.2.1, f t.2.2.2.2)

private theorem map_fold {α β : Type} (f : α → β) (z : α) (step : Nat → Nat → Quint α → α)
    (step' : Nat → Nat → Quint β → β)
    (hs : ∀ tag p cs, f (step tag p cs) = step' tag p (qmap f cs)) (n : Nat) :
    f (fold z step n) = fold (f z) step' n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fold, fold]
    split
    · rfl
    · rename_i hn
      have hm : (n-1)/8 < n := (Nat.div_le_self _ _).trans_lt (by omega)
      have hr := (Nat.unpair_right_le ((n-1)/8)).trans_lt hm
      have hr₂ := (Nat.unpair_right_le ((n-1)/8).unpair.2).trans_lt hr
      have hr₃ := (Nat.unpair_right_le ((n-1)/8).unpair.2.unpair.2).trans_lt hr₂
      have hr₄ := (Nat.unpair_right_le ((n-1)/8).unpair.2.unpair.2.unpair.2).trans_lt hr₃
      rw [hs]
      simp only [qmap]
      rw [ih _ ((Nat.unpair_left_le _).trans_lt hr), ih _ ((Nat.unpair_left_le _).trans_lt hr₂),
        ih _ ((Nat.unpair_left_le _).trans_lt hr₃), ih _ ((Nat.unpair_left_le _).trans_lt hr₄),
        ih _ ((Nat.unpair_right_le _).trans_lt hr₄)]

private def assembleNat (tag p : Nat) (cs : Quint Nat) : Nat :=
  if tag = 0 then node 0 (putNat (readNat ((Γ' → Bool) × K' × K') p)) (cs.1,0,0,0,0)
  else if tag = 1 then node 1 (putNat (readNat ((Γ' → Bool) × K') p)) (cs.1,0,0,0,0)
  else if tag = 2 then node 2 0 (cs.1,0,0,0,0)
  else if tag = 3 then node 3 (putNat (readNat (K' × (Option Γ' → Option Γ')) p)) (cs.1,0,0,0,0)
  else if tag = 4 then node 4 0 cs
  else if tag = 5 then node 5 0 (cs.1,0,0,0,0)
  else if tag = 6 then node 6 0 (cs.1,cs.2.1,0,0,0)
  else node 7 (putNat (readNat Cont' p)) (0,0,0,0,0)

private theorem pr_node {β : Type} [Primcodable β] {t p a b c d e : β → Nat}
    (ht : Primrec t) (hp : Primrec p) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (he : Primrec e) : Primrec (fun x => node (t x) (p x) (a x,b x,c x,d x,e x)) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp hp (Primrec₂.natPair.comp ha (Primrec₂.natPair.comp hb
      (Primrec₂.natPair.comp hc (Primrec₂.natPair.comp hd he)))))) ht) (Primrec.const 1)

private theorem pr_payload (α : Type) [Primcodable α] [Inhabited α] :
    Primrec (fun n => putNat (readNat α n)) :=
  Primrec.encode.comp (Primrec.option_getD.comp Primrec.decode (Primrec.const default))

theorem normalizationPrimitiveRecursive : Targets.NormalizationPrimitiveRecursive := by
  have hs : Primrec (fun x : Nat × Nat × Quint Nat => assembleNat x.1 x.2.1 x.2.2) := by
    have he (k : Nat) : PrimrecPred (fun x : Nat × Nat × Quint Nat => x.1=k) :=
      Primrec.eq.comp Primrec.fst (Primrec.const k)
    have hp : Primrec (fun x : Nat × Nat × Quint Nat => x.2.1) := Primrec.fst.comp Primrec.snd
    have hg : Primrec (fun x : Nat × Nat × Quint Nat => x.2.2) := Primrec.snd.comp Primrec.snd
    have ha := Primrec.fst.comp hg
    have hb := Primrec.fst.comp (Primrec.snd.comp hg)
    have hc := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hg))
    have hd := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hg)))
    have hi := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hg)))
    have h0 := Primrec.const (α := Nat × Nat × Quint Nat) 0
    have hm := pr_node (Primrec.const 0) ((pr_payload ((Γ' → Bool) × K' × K')).comp hp) ha h0 h0 h0 h0
    have hcl := pr_node (Primrec.const 1) ((pr_payload ((Γ' → Bool) × K')).comp hp) ha h0 h0 h0 h0
    have hcp := pr_node (Primrec.const 2) h0 ha h0 h0 h0 h0
    have hps := pr_node (Primrec.const 3) ((pr_payload (K' × (Option Γ' → Option Γ'))).comp hp) ha h0 h0 h0 h0
    have hrd := pr_node (Primrec.const 4) h0 ha hb hc hd hi
    have hsu := pr_node (Primrec.const 5) h0 ha h0 h0 h0 h0
    have hpr := pr_node (Primrec.const 6) h0 ha hb h0 h0 h0
    have hrt := pr_node (Primrec.const 7) ((pr_payload Cont').comp hp) h0 h0 h0 h0 h0
    exact Primrec.ite (he 0) hm (Primrec.ite (he 1) hcl (Primrec.ite (he 2) hcp
      (Primrec.ite (he 3) hps (Primrec.ite (he 4) hrd (Primrec.ite (he 5) hsu (Primrec.ite (he 6) hpr hrt))))))
  apply (foldPrimitiveRecursive Nat (code (.ret .halt)) assembleNat hs).of_eq
  intro n
  exact (map_fold code (.ret .halt) assemble assembleNat
    (by intro tag p cs; dsimp [assemble, assembleNat]; split_ifs <;> rfl) n).symm

instance labelPrimcodable : Primcodable Label where
  encode := code
  decode := fun n => some (decode n)
  encodek := fun q => congrArg some (roundtrip q)
  prim := by
    have h := Primrec.nat_iff.mp (Primrec.succ.comp normalizationPrimitiveRecursive)
    exact h.of_eq (fun n => rfl)

theorem actualPrimcodable : Targets.ActualPrimcodable := ⟨labelPrimcodable, rfl⟩
end LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodec
