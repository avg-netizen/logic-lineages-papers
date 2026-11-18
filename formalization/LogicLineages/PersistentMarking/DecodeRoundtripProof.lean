import LogicLineages.PersistentMarking.OpeningFoundationProof
namespace LogicLineages.PersistentMarking.DecodeRoundtripProof
open Spine NameBridge

inductive DistinctEnv : List Name → Prop where
  | nil : DistinctEnv []
  | cons : nameLookup env n = none → DistinctEnv env → DistinctEnv (n::env)

def SafeEnv (env : List Name) (q : Expr) : Prop :=
  ∀ n, freeOccurs n q = true → nameLookup env n = none

def SafeArgs (env : List Name) (qs : Args) : Prop :=
  ∀ n, freeOccursArgs n qs = true → nameLookup env n = none

theorem lookupAt (env : List Name) (hd : DistinctEnv env) (i : Nat) (n : Name)
    (h : env[i]? = some n) : nameLookup env n = some i := by
  cases env with
  | nil => simp at h
  | cons m ms =>
    cases hd with
    | cons hn hd =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst n
        simp [nameLookup]
      | succ i =>
        have hi := lookupAt ms hd i n h
        have hne : n ≠ m := by intro he; subst n; rw [hn] at hi; contradiction
        simp [nameLookup, hne, hi]
termination_by env.length

theorem getType (env : List Name) (i : Nat) (σ : Ty)
    (h : (env.map Prod.fst)[i]? = some σ) : ∃ x, env[i]? = some (σ,x) := by
  cases env with
  | nil => simp at h
  | cons n ns =>
    rcases n with ⟨δ,x⟩
    cases i with
    | zero =>
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h
      subst σ
      exact ⟨x,rfl⟩
    | succ i => exact getType ns i σ h
termination_by env.length

theorem lookupAbove (env : List Name) (σ : Ty) (x : Nat) (h : maxEnv env < x) :
    nameLookup env (σ,x) = none := by
  cases env with
  | nil => rfl
  | cons n ns =>
    rcases n with ⟨δ,y⟩
    have hy : y < x := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
    have hn : maxEnv ns < x := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
    have he : (σ,x) ≠ (δ,y) := by
      intro he
      have hh := congrArg Prod.snd he
      simp only at hh
      omega
    simp only [nameLookup, he, if_false, lookupAbove ns σ x hn, Option.map_none]
termination_by env.length

mutual
 theorem roundtrip (env : List Name) (q : Expr) (hd : DistinctEnv env)
    (hs : SafeEnv env q) (hc : Scoped (env.map Prod.fst) q) :
    encode env (decode env q) = q := by
  cases q with
  | free σ x =>
    have hl := hs (σ,x) (by simp [freeOccurs])
    simp only [decode, encode, hl]
  | bound σ i =>
    obtain ⟨x,hx⟩ := getType env i σ hc
    have hl := lookupAt env hd i (σ,x) hx
    simp only [decode, hx, encode, hl]
  | lam σ body =>
    let x := freshName env body
    have hx : maxEnv env < x := by dsimp [x, freshName]; omega
    have hb : maxFreeName body < x := by dsimp [x, freshName]; omega
    have hf := OpeningFoundationProof.aboveFresh σ x body hb
    have hd' : DistinctEnv ((σ,x)::env) := .cons (lookupAbove env σ x hx) hd
    have hs' : SafeEnv ((σ,x)::env) body := by
      intro n hn
      have hne : n ≠ (σ,x) := by intro he; subst n; rw [hf] at hn; contradiction
      have hh := hs n hn
      simp only [nameLookup, hne, if_false, hh, Option.map_none]
    have ih := roundtrip ((σ,x)::env) body hd' hs' hc
    exact congrArg (Expr.lam σ) ih
  | head f base => exact congrArg (Expr.head f) (roundtripArgs env base hd hs hc)
  | marked f τ base extras =>
    have hs1 : SafeArgs env base := by
      intro n hn
      apply hs n
      simp only [freeOccurs, hn, Bool.true_or]
    have hs2 : SafeArgs env extras := by
      intro n hn
      apply hs n
      simp only [freeOccurs, hn, Bool.or_true]
    simp only [decode, encode, roundtripArgs env base hd hs1 hc.1,
      roundtripArgs env extras hd hs2 hc.2]
 termination_by sizeOf q
 theorem roundtripArgs (env : List Name) (qs : Args) (hd : DistinctEnv env)
    (hs : SafeArgs env qs) (hc : ScopedArgs (env.map Prod.fst) qs) :
    encodeArgs env (decodeArgs env qs) = qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hs1 : SafeEnv env q := by
      intro n hn
      apply hs n
      simp only [freeOccursArgs, hn, Bool.true_or]
    have hs2 : SafeArgs env qs := by
      intro n hn
      apply hs n
      simp only [freeOccursArgs, hn, Bool.or_true]
    simp only [decodeArgs, encodeArgs, roundtrip env q hd hs1 hc.1,
      roundtripArgs env qs hd hs2 hc.2]
 termination_by sizeOf qs
end

theorem encodeDecodeScoped : BridgeTargets.EncodeDecodeScoped := by
  intro q hc
  exact roundtrip [] q .nil (by intro n _; rfl) hc
end LogicLineages.PersistentMarking.DecodeRoundtripProof
