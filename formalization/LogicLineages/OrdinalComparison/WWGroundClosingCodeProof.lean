module
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosingCode.Proof
open SyntaxCode GroundClosing

private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

theorem rawExact : Targets.RawExact := by
  intro depth t
  induction t generalizing depth with
  | var i =>
      rw [code,closeCode]
      simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left i (by decide : 0<8), if_pos rfl]
      by_cases h : i<depth <;> simp [closeRaw,h,code]
  | zero => rw [code,closeCode]; simp [closeRaw,code]
  | succ => rw [code,closeCode]; simp [closeRaw,code]
  | caseC τ =>
      rw [code,closeCode]
      simp [mod_tag τ 3 (by omega),div_tag τ 3 (by omega),closeRaw,code]
  | recC τ =>
      rw [code,closeCode]
      simp [mod_tag τ 4 (by omega),div_tag τ 4 (by omega),closeRaw,code]
  | app f a hf ha =>
      rw [code,closeCode]
      simp [mod_tag _ 5 (by omega),div_tag _ 5 (by omega),Nat.unpair_pair,hf,ha,closeRaw,code]
  | lam σ b hb =>
      rw [code,closeCode]
      simp [mod_tag _ 6 (by omega),div_tag _ 6 (by omega),Nat.unpair_pair,hb,closeRaw,code]

theorem compatible_lift {Γ Δ : List Ty} {τ : Ty} {depth : Nat}
    {r : GroundMap Γ Δ} (h : Compatible depth r) : Compatible (depth+1) (@GroundMap.lift Γ Δ τ r) := by
  intro σ x
  cases x with
  | here => simp [GroundMap.lift,Image.source,erase,closeRaw,SourceTypedPorts.variableIndex]
  | there x =>
      have hx := h x
      cases he : r x with
      | var y =>
          simp only [he,Image.source,erase,closeRaw] at hx
          by_cases hi : SourceTypedPorts.variableIndex x < depth
          · simp only [hi,if_pos,Raw.var.injEq] at hx
            simp [GroundMap.lift,he,Image.weaken,Image.source,erase,closeRaw,
              SourceTypedPorts.variableIndex,hx,hi]
          · simp [hi] at hx
      | zero =>
          simp only [he,Image.source,erase,closeRaw] at hx
          by_cases hi : SourceTypedPorts.variableIndex x < depth
          · simp [hi] at hx
          · simp [GroundMap.lift,he,Image.weaken,Image.source,erase,closeRaw,
              SourceTypedPorts.variableIndex,hi]

theorem source_lift {Γ Δ τ} (r : GroundMap Γ Δ) :
    (@GroundMap.source (τ :: Γ) (τ :: Δ) (GroundMap.lift r)) =
      (@Substitution.lift Empty Empty.elim Γ Δ τ (@GroundMap.source Γ Δ r)) := by
  funext σ x
  cases x with
  | here => rfl
  | there x => cases h : r x <;> simp [GroundMap.lift, GroundMap.source,
      Substitution.lift, Image.weaken, Image.source, h, Source.Term.rename, Renaming.weaken]

theorem erase_substitute {Γ Δ : List Ty} {τ : Ty} (depth : Nat)
    (r : GroundMap Γ Δ) (h : Compatible depth r) (t : OriginalTerm Γ τ) :
    erase (t.substitute r.source) = closeRaw depth (erase t) := by
  induction t generalizing Δ depth with
  | var x => exact h x
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ => rfl
  | app f a hf ha => simp only [Source.Term.substitute,erase,closeRaw,hf _ r h,ha _ r h]
  | lam b hb =>
      simp only [Source.Term.substitute,← source_lift,erase,closeRaw]
      rw [hb (depth+1) r.lift (compatible_lift h)]
  | ranked s _ => nomatch s

theorem typedExact : Targets.TypedExact := by
  intro Γ Δ τ depth r h t
  rw [encodeTerm,rawExact,encodeTerm,erase_substitute depth r h t]

theorem closedExact : Targets.ClosedExact := by
  intro Γ τ r t
  apply typedExact Γ [] τ 0 r _ t
  intro σ x
  cases he : r x with
  | var y => nomatch y
  | zero => simp [he,Image.source,erase,closeRaw]

theorem primitiveRecursive : Targets.PrimitiveRecursive := by
  let children : (Nat×Nat) → List (Nat×Nat) := fun s =>
    if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
    else if s.2%8=6 then [(s.1+1,(s.2/8).unpair.2)] else []
  let base : (Nat×Nat) → Nat := fun s =>
    if s.2%8=0 then if s.2/8<s.1 then s.2 else 1
    else if s.2%8=1 then 1
    else if s.2%8=2 then if s.2/8=0 then 2 else 1
    else if s.2%8=3 then s.2
    else if s.2%8=4 then s.2 else 1
  let assemble : (Nat×Nat) → List Nat → Option Nat := fun s rs => some
    (if s.2%8=5 then 8*Nat.pair (rs.getD 0 1) (rs.getD 1 1)+5
    else if s.2%8=6 then 8*Nat.pair (s.2/8).unpair.1 (rs.getD 0 1)+6
    else base s)
  have hn (k : Nat) : Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const k)
  have htag : Primrec (fun s : Nat×Nat => s.2%8) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hpay : Primrec (fun s : Nat×Nat => s.2/8) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Nat×Nat => s.2%8=k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hz : PrimrecPred (fun s : Nat×Nat => s.2/8=0) :=
    Primrec.eq.comp hpay (Primrec.const 0)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp ((Primrec.succ.comp Primrec.fst).pair hr) (Primrec.const []))
      (Primrec.const []))
  have hb : Primrec base := Primrec.ite (ht 0)
    (Primrec.ite (Primrec.nat_lt.comp hpay Primrec.fst) Primrec.snd (Primrec.const 1))
    (Primrec.ite (ht 1) (Primrec.const 1)
    (Primrec.ite (ht 2) (Primrec.ite hz (Primrec.const 2) (Primrec.const 1))
    (Primrec.ite (ht 3) Primrec.snd
    (Primrec.ite (ht 4) Primrec.snd (Primrec.const 1)))))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat×Nat)×List Nat => p.2.getD k 1) :=
      (Primrec.list_getD (1 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 5).comp Primrec.fst)
      ((hn 5).comp ((hg 0).pair (hg 1)))
      (Primrec.ite ((ht 6).comp Primrec.fst)
        ((hn 6).comp ((hl.comp Primrec.fst).pair (hg 0))) (hb.comp Primrec.fst)))
  apply Primrec.nat_omega_rec' (fun s : Nat×Nat => closeCode s.1 s.2) Primrec.snd hc ha
  · intro s t hmem
    change t.2 < s.2
    by_cases h5 : s.2%8=5
    · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2%8=6
      · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro s
    conv_rhs => rw [closeCode]
    have ht : s.2%8=0 ∨ s.2%8=1 ∨ s.2%8=2 ∨ s.2%8=3 ∨ s.2%8=4 ∨ s.2%8=5 ∨ s.2%8=6 ∨ s.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,base,h]
end LogicLineages.OrdinalComparison.Source.GroundClosingCode.Proof
