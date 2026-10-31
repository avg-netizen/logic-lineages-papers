module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof

private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

theorem decodeEncode : Targets.DecodeEncode := by
  intro r
  induction r with
  | var i => rw [code,decode]; simp
  | zero => rw [code,decode]; simp
  | succ => rw [code,decode]; simp
  | caseC τ =>
      rw [code,decode]
      simp [mod_tag τ 3 (by omega),div_tag τ 3 (by omega)]
  | recC τ =>
      rw [code,decode]
      simp [mod_tag τ 4 (by omega),div_tag τ 4 (by omega)]
  | app f a hf ha =>
      rw [code,decode]
      simp [mod_tag _ 5 (by omega),div_tag _ 5 (by omega),Nat.unpair_pair,hf,ha]
  | lam σ b hb =>
      rw [code,decode]
      simp [mod_tag _ 6 (by omega),div_tag _ 6 (by omega),Nat.unpair_pair,hb]

theorem encodeDecode : Targets.EncodeDecode := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro r h
      have ht : n%8=0 ∨ n%8=1 ∨ n%8=2 ∨ n%8=3 ∨ n%8=4 ∨ n%8=5 ∨ n%8=6 ∨ n%8=7 := by omega
      rw [decode] at h
      rcases ht with ht|ht|ht|ht|ht|ht|ht|ht
      · have he : Raw.var (n/8) = r := by simpa [ht] using h
        subst r
        simp only [code]
        omega
      · by_cases hz : n/8=0
        · have he : Raw.zero = r := by simpa [ht,hz] using h
          subst r
          simp only [code]
          omega
        · simp [ht,hz] at h
      · by_cases hz : n/8=0
        · have he : Raw.succ = r := by simpa [ht,hz] using h
          subst r
          simp only [code]
          omega
        · simp [ht,hz] at h
      · have he : Raw.caseC (n/8) = r := by simpa [ht] using h
        subst r
        simp only [code]
        omega
      · have he : Raw.recC (n/8) = r := by simpa [ht] using h
        subst r
        simp only [code]
        omega
      · have hn : 0<n := by omega
        have hd : n/8<n := Nat.div_lt_self hn (by decide)
        have hl := (Nat.unpair_left_le (n/8)).trans_lt hd
        have hr := (Nat.unpair_right_le (n/8)).trans_lt hd
        cases hf : decode (n/8).unpair.1 with
        | none => simp [ht,hf] at h
        | some f =>
          cases ha : decode (n/8).unpair.2 with
          | none => simp [ht,hf,ha] at h
          | some a =>
            have he : Raw.app f a = r := by simpa [ht,hf,ha] using h
            subst r
            rw [code,ih _ hl _ hf,ih _ hr _ ha,Nat.pair_unpair]
            omega
      · have hn : 0<n := by omega
        have hd : n/8<n := Nat.div_lt_self hn (by decide)
        have hr := (Nat.unpair_right_le (n/8)).trans_lt hd
        cases hb : decode (n/8).unpair.2 with
        | none => simp [ht,hb] at h
        | some b =>
          have he : Raw.lam (n/8).unpair.1 b = r := by simpa [ht,hb] using h
          subst r
          rw [code,ih _ hr _ hb,Nat.pair_unpair]
          omega
      · simp [ht] at h

theorem codeInjective : Targets.CodeInjective := by
  intro a b h
  have hd := congrArg decode h
  rw [decodeEncode a,decodeEncode b] at hd
  exact Option.some.inj hd

theorem constructorsPrimitiveRecursive : Targets.ConstructorsPrimitiveRecursive := by
  have hm : Primrec (fun n : Nat => 8*n) := Primrec.nat_mul.comp (Primrec.const 8) Primrec.id
  have ht (k : Nat) : Primrec (fun n : Nat => 8*n+k) :=
    Primrec.nat_add.comp hm (Primrec.const k)
  exact ⟨hm,ht 3,ht 4,(ht 5).comp Primrec₂.natPair,(ht 6).comp Primrec₂.natPair⟩
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof
