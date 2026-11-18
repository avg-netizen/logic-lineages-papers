import LogicLineages.PersistentMarking.BridgeTargets
namespace LogicLineages.PersistentMarking.AlphaEncodingProof
open Spine NameBridge

theorem lookupAppend (left right : List Name) (n : Name) :
    nameLookup (left++right) n =
      match nameLookup left n with
      | some i => some i
      | none => (nameLookup right n).map (fun i => left.length+i) := by
  induction left with
  | nil => simp [nameLookup]
  | cons m ms ih =>
    by_cases he : n = m
    · simp [nameLookup, he]
    · cases hl : nameLookup ms n <;> cases hr : nameLookup right n <;>
        simp [nameLookup, he, hl, ih, hr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem lookupSlot (locals env : List Name) (n : Name) (h : nameLookup locals n = none) :
    nameLookup (locals++n::env) n = some locals.length := by
  simp [lookupAppend, h, nameLookup]

theorem lookupDifferent (locals env : List Name) (n old new : Name)
    (ho : n ≠ old) (hn : n ≠ new) :
    nameLookup (locals++new::env) n = nameLookup (locals++old::env) n := by
  simp only [lookupAppend]
  cases hl : nameLookup locals n with
  | some i => rfl
  | none => simp [nameLookup, ho, hn]

mutual
 theorem encodeAgree (env₁ env₂ : List Name) (q : Term)
    (h : ∀ n, nameOccurs n q = true → nameLookup env₁ n = nameLookup env₂ n) :
    encode env₁ q = encode env₂ q := by
  cases q with
  | var σ x =>
    have hh := h (σ,x) (by simp [nameOccurs])
    simp only [encode, hh]
  | lam σ x body =>
    apply congrArg (Expr.lam σ)
    apply encodeAgree ((σ,x)::env₁) ((σ,x)::env₂) body
    intro n hn
    by_cases he : n = (σ,x)
    · simp [nameLookup, he]
    · have hh := h n (by simp [nameOccurs, hn])
      simp [nameLookup, he, hh]
  | head f base => exact congrArg (Expr.head f) (encodeArgsAgree env₁ env₂ base h)
  | marked f τ base extras =>
    have hb := encodeArgsAgree env₁ env₂ base (fun n hn => h n (by simp [nameOccurs, hn]))
    have he := encodeArgsAgree env₁ env₂ extras (fun n hn => h n (by simp [nameOccurs, hn]))
    simp only [encode, hb, he]
 termination_by sizeOf q
 theorem encodeArgsAgree (env₁ env₂ : List Name) (qs : List Term)
    (h : ∀ n, namesOccur n qs = true → nameLookup env₁ n = nameLookup env₂ n) :
    encodeArgs env₁ qs = encodeArgs env₂ qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hq := encodeAgree env₁ env₂ q (fun n hn => h n (by simp [namesOccur, hn]))
    have hqs := encodeArgsAgree env₁ env₂ qs (fun n hn => h n (by simp [namesOccur, hn]))
    simp only [encodeArgs, hq, hqs]
 termination_by sizeOf qs
end

mutual
 theorem renameEncode (env locals : List Name) (σ : Ty) (x z : Nat) (q : Term)
    (ho : nameLookup locals (σ,x) = none) (hn : nameLookup locals (σ,z) = none)
    (hf : nameOccurs (σ,z) q = false) :
    encode (locals++(σ,z)::env) (renameFree (σ,x) (σ,z) q) =
      encode (locals++(σ,x)::env) q := by
  cases q with
  | var δ y =>
    have hnew : (δ,y) ≠ (σ,z) := by
      intro he
      cases he
      simp [nameOccurs] at hf
    by_cases hold : (δ,y) = (σ,x)
    · cases hold
      simp [renameFree, encode, lookupSlot locals env (σ,x) ho, lookupSlot locals env (σ,z) hn]
    · simp only [renameFree, hold, if_false, encode,
        lookupDifferent locals env (δ,y) (σ,x) (σ,z) hold hnew]
  | lam δ y body =>
    have hnew : (δ,y) ≠ (σ,z) := by
      intro he
      cases he
      simp [nameOccurs] at hf
    have hfbody : nameOccurs (σ,z) body = false := by
      simpa [nameOccurs, Ne.symm hnew] using hf
    by_cases hold : (δ,y) = (σ,x)
    · simp only [renameFree, hold, if_pos, encode]
      apply congrArg (Expr.lam δ)
      apply encodeAgree
      intro n hbody
      have hnz : n ≠ (σ,z) := by intro he; subst n; rw [hfbody] at hbody; contradiction
      by_cases hny : n = (δ,y)
      · have hnx : n = (σ,x) := hny.trans hold
        simp [nameLookup, hnx]
      · have hnx : n ≠ (σ,x) := by simpa only [← hold] using hny
        simp only [nameLookup, hnx, if_false,
          lookupDifferent locals env n (σ,x) (σ,z) hnx hnz]
    · have ho' : nameLookup ((δ,y)::locals) (σ,x) = none := by
        simp [nameLookup, Ne.symm hold, ho]
      have hn' : nameLookup ((δ,y)::locals) (σ,z) = none := by
        simp [nameLookup, Ne.symm hnew, hn]
      simp only [renameFree, hold, if_false, encode]
      exact congrArg (Expr.lam δ) (renameEncode env ((δ,y)::locals) σ x z body ho' hn' hfbody)
  | head f base => exact congrArg (Expr.head f) (renameArgsEncode env locals σ x z base ho hn hf)
  | marked f τ base extras =>
    have hb : namesOccur (σ,z) base = false := by cases h : namesOccur (σ,z) base <;> simp_all [nameOccurs]
    have he : namesOccur (σ,z) extras = false := by cases h : namesOccur (σ,z) extras <;> simp_all [nameOccurs]
    simp only [renameFree, encode, renameArgsEncode env locals σ x z base ho hn hb,
      renameArgsEncode env locals σ x z extras ho hn he]
 termination_by sizeOf q
 theorem renameArgsEncode (env locals : List Name) (σ : Ty) (x z : Nat) (qs : List Term)
    (ho : nameLookup locals (σ,x) = none) (hn : nameLookup locals (σ,z) = none)
    (hf : namesOccur (σ,z) qs = false) :
    encodeArgs (locals++(σ,z)::env) (renameFreeArgs (σ,x) (σ,z) qs) =
      encodeArgs (locals++(σ,x)::env) qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hq : nameOccurs (σ,z) q = false := by cases h : nameOccurs (σ,z) q <;> simp_all [namesOccur]
    have hqs : namesOccur (σ,z) qs = false := by cases h : namesOccur (σ,z) qs <;> simp_all [namesOccur]
    simp only [renameFreeArgs, encodeArgs, renameEncode env locals σ x z q ho hn hq,
      renameArgsEncode env locals σ x z qs ho hn hqs]
 termination_by sizeOf qs
end

theorem alphaEncode (a b : Term) (h : Alpha a b) : ∀ env, encode env a = encode env b := by
  apply Alpha.rec (motive_1 := fun a b _ => ∀ env, encode env a = encode env b)
    (motive_2 := fun as bs _ => ∀ env, encodeArgs env as = encodeArgs env bs) (t := h)
  · intro q env; rfl
  · intro q r h ih env; exact (ih env).symm
  · intro q r s h₁ h₂ ih₁ ih₂ env; exact (ih₁ env).trans (ih₂ env)
  · intro q r σ x h ih env; exact congrArg (Expr.lam σ) (ih ((σ,x)::env))
  · intro qs rs f h ih env; exact congrArg (Expr.head f) (ih env)
  · intro qs rs es fs f τ h₁ h₂ ih₁ ih₂ env
    simp only [encode, ih₁ env, ih₂ env]
  · intro σ z body x hf _ env
    exact congrArg (Expr.lam σ) (renameEncode env [] σ x z body rfl rfl hf).symm
  · intro env; rfl
  · intro q r qs rs h₁ h₂ ih₁ ih₂ env
    simp only [encodeArgs, ih₁ env, ih₂ env]

theorem encodeRespectsAlpha : BridgeTargets.EncodeRespectsAlpha := by
  intro env a b h
  exact alphaEncode a b h env
end LogicLineages.PersistentMarking.AlphaEncodingProof
