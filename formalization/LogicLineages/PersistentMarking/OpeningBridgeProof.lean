import LogicLineages.PersistentMarking.AlphaEncodingProof
namespace LogicLineages.PersistentMarking.OpeningBridgeProof
open Spine NameBridge

def freeNames : List Name → Args
  | [] => .nil
  | (σ,x)::ns => .cons (.free σ x) (freeNames ns)

theorem lookupIndex (env : List Name) (n : Name) (i : Nat) (h : nameLookup env n = some i) :
    env[i]? = some n ∧ i < env.length := by
  cases env with
  | nil => simp [nameLookup] at h
  | cons m ms =>
    by_cases he : n = m
    · subst n
      simp [nameLookup] at h
      subst i
      exact ⟨rfl, by simp⟩
    · cases hl : nameLookup ms n with
      | none => simp [nameLookup, he, hl] at h
      | some j =>
        simp [nameLookup, he, hl] at h
        subst i
        have ih := lookupIndex ms n j hl
        exact ⟨ih.1, Nat.succ_lt_succ ih.2⟩
termination_by env.length

theorem freeNamesGet (env : List Name) (i : Nat) (n : Name) (h : env[i]? = some n) :
    (freeNames env).get i = some (.free n.1 n.2) := by
  cases env with
  | nil => simp at h
  | cons m ms =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst n
      cases m
      rfl
    | succ i =>
      cases m
      exact freeNamesGet ms i n h
termination_by env.length

mutual
 theorem openEncoding (env locals : List Name) (q : Term) :
    substitute (freeNames env) locals.length (encode (locals++env) q) = encode locals q := by
  cases q with
  | var σ x =>
    cases hl : nameLookup locals (σ,x) with
    | some i =>
      have hi := (lookupIndex locals (σ,x) i hl).2
      simp [encode, AlphaEncodingProof.lookupAppend, hl, substitute, hi]
    | none =>
      cases he : nameLookup env (σ,x) with
      | none => simp [encode, AlphaEncodingProof.lookupAppend, hl, he, substitute]
      | some i =>
        have hg := freeNamesGet env i (σ,x) (lookupIndex env (σ,x) i he).1
        have hi : ¬ locals.length+i < locals.length := by omega
        simp [encode, AlphaEncodingProof.lookupAppend, hl, he, substitute, hi, hg, shift]
  | lam σ x body => exact congrArg (Expr.lam σ) (openEncoding env ((σ,x)::locals) body)
  | head f base => exact congrArg (Expr.head f) (openArgsEncoding env locals base)
  | marked f τ base extras =>
    simp only [encode, substitute, openArgsEncoding env locals base, openArgsEncoding env locals extras]
 termination_by sizeOf q
 theorem openArgsEncoding (env locals : List Name) (qs : List Term) :
    substituteArgs (freeNames env) locals.length (encodeArgs (locals++env) qs) = encodeArgs locals qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [encodeArgs, substituteArgs, openEncoding env locals q, openArgsEncoding env locals qs]
 termination_by sizeOf qs
end

theorem openingBridge : BridgeTargets.OpeningBridge := by
  intro σ x z body hf _
  have hr := AlphaEncodingProof.renameEncode [] [] σ x z body rfl rfl hf
  have hh := congrArg (substitute (.cons (.free σ z) .nil) 0) hr
  exact (openEncoding [(σ,z)] [] (renameFree (σ,x) (σ,z) body)).symm.trans hh
end LogicLineages.PersistentMarking.OpeningBridgeProof
