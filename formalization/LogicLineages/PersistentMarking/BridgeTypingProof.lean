import LogicLineages.PersistentMarking.BridgeTargets
namespace LogicLineages.PersistentMarking.BridgeTypingProof
open Spine NameBridge

theorem lookupType (env : List Name) (n : Name) (i : Nat)
    (h : nameLookup env n = some i) :
    BoundContext.«prefix» (env.map Prod.fst) EmptyContext i = some n.1 := by
  cases env with
  | nil => simp [nameLookup] at h
  | cons y ys =>
    by_cases he : n = y
    · subst n
      simp [nameLookup] at h
      subst i
      rfl
    · cases hl : nameLookup ys n with
      | none => simp [nameLookup, he, hl] at h
      | some j =>
        simp only [nameLookup, he, if_false, hl, Option.map_some, Option.some.injEq] at h
        subst i
        exact lookupType ys n j hl
termination_by env.length

mutual
 theorem encodeTyped (env : List Name) (q : Term) (σ : Ty) (h : NamedTyped q σ) :
    Typed (BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (encode env q) σ := by
  cases q with
  | var δ x =>
    cases h
    cases hl : nameLookup env (σ,x) with
    | none => simpa only [encode, hl] using (Typed.free (Γ := BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (σ := σ) (x := x))
    | some i => simpa only [encode, hl] using Typed.bound (lookupType env (σ,x) i hl)
  | lam δ x body =>
    cases h with
    | lam hb => exact .lam (encodeTyped ((δ,x)::env) body _ hb)
  | head f base =>
    cases h with
    | head hb => exact .head (encodeBase env base _ hb)
  | marked f τ base extras =>
    cases h with
    | marked hb he => exact .marked (encodeBase env base _ hb) (encodeExtras env extras he)
 termination_by sizeOf q
 theorem encodeBase (env : List Name) (qs : List Term) (types : List Ty) (h : NamedBase qs types) :
    BaseTyped (BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (encodeArgs env qs) types := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (encodeTyped env q _ hq) (encodeBase env qs _ hqs)
 termination_by sizeOf qs
 theorem encodeExtras (env : List Name) (qs : List Term) (h : NamedExtras qs) :
    ExtrasTyped (BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (encodeArgs env qs) := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (encodeTyped env q _ hq) (encodeExtras env qs hqs)
 termination_by sizeOf qs
end

mutual
 theorem encodeReflects (env : List Name) (q : Term) (σ : Ty)
    (h : Typed (BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (encode env q) σ) : NamedTyped q σ := by
  cases q with
  | var δ x =>
    cases hl : nameLookup env (δ,x) with
    | none => simp only [encode, hl] at h; cases h; exact .var
    | some i => simp only [encode, hl] at h; cases h; exact .var
  | lam δ x body =>
    cases h with
    | lam hb => exact .lam (encodeReflects ((δ,x)::env) body _ hb)
  | head f base =>
    cases h with
    | head hb => exact .head (encodeBaseReflects env base _ hb)
  | marked f τ base extras =>
    cases h with
    | marked hb he => exact .marked (encodeBaseReflects env base _ hb) (encodeExtrasReflects env extras he)
 termination_by sizeOf q
 theorem encodeBaseReflects (env : List Name) (qs : List Term) (types : List Ty)
    (h : BaseTyped (BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (encodeArgs env qs) types) : NamedBase qs types := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (encodeReflects env q _ hq) (encodeBaseReflects env qs _ hqs)
 termination_by sizeOf qs
 theorem encodeExtrasReflects (env : List Name) (qs : List Term)
    (h : ExtrasTyped (BoundContext.«prefix» (env.map Prod.fst) EmptyContext) (encodeArgs env qs)) : NamedExtras qs := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (encodeReflects env q _ hq) (encodeExtrasReflects env qs hqs)
 termination_by sizeOf qs
end

theorem encodeTypingExact : BridgeTargets.EncodeTypingExact := by
  intro env q σ
  exact ⟨encodeTyped env q σ, encodeReflects env q σ⟩

mutual
 theorem decodeTyped (Γ : BoundContext) (env : List Name) (q : Expr) (σ : Ty)
    (h : Typed Γ q σ) : NamedTyped (decode env q) σ := by
  cases q with
  | free δ x => cases h; exact .var
  | bound δ i =>
    cases h
    cases he : env[i]? with
    | none => simp only [decode, he]; exact .var
    | some n => simp only [decode, he]; exact .var
  | lam δ body =>
    cases h with
    | lam hb => exact .lam (decodeTyped _ ((δ,freshName env body)::env) body _ hb)
  | head f base =>
    cases h with
    | head hb => exact .head (decodeBase Γ env base _ hb)
  | marked f τ base extras =>
    cases h with
    | marked hb he => exact .marked (decodeBase Γ env base _ hb) (decodeExtras Γ env extras he)
 termination_by sizeOf q
 theorem decodeBase (Γ : BoundContext) (env : List Name) (qs : Args) (types : List Ty)
    (h : BaseTyped Γ qs types) : NamedBase (decodeArgs env qs) types := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (decodeTyped Γ env q _ hq) (decodeBase Γ env qs _ hqs)
 termination_by sizeOf qs
 theorem decodeExtras (Γ : BoundContext) (env : List Name) (qs : Args)
    (h : ExtrasTyped Γ qs) : NamedExtras (decodeArgs env qs) := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs =>
    cases h with
    | cons hq hqs => exact .cons (decodeTyped Γ env q _ hq) (decodeExtras Γ env qs hqs)
 termination_by sizeOf qs
end

theorem decodeTyping : BridgeTargets.DecodeTyping := decodeTyped EmptyContext []

mutual
 theorem encodeValidity (S : Signature) (env : List Name) (q : Term) :
    NamedValid S q ↔ Valid S (encode env q) := by
  cases q with
  | var σ x =>
    cases hl : nameLookup env (σ,x) <;> simp [encode, hl, NamedValid, Valid]
  | lam σ x body => exact encodeValidity S ((σ,x)::env) body
  | head f base => simp only [NamedValid, encode, Valid, encodeArgsValidity S env base]
  | marked f τ base extras =>
    simp only [NamedValid, encode, Valid, encodeArgsValidity S env base, encodeArgsValidity S env extras]
 termination_by sizeOf q
 theorem encodeArgsValidity (S : Signature) (env : List Name) (qs : List Term) :
    NamedValidArgs S qs ↔ ValidArgs S (encodeArgs env qs) := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [NamedValidArgs, encodeArgs, ValidArgs, encodeValidity S env q, encodeArgsValidity S env qs]
 termination_by sizeOf qs
end

theorem encodeValidityExact : BridgeTargets.EncodeValidityExact := encodeValidity
end LogicLineages.PersistentMarking.BridgeTypingProof
