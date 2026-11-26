import LogicLineages.PersistentMarking.AlphaSizeProof
import LogicLineages.PersistentMarking.OpeningBridgeProof
import LogicLineages.PersistentMarking.DecodeRoundtripProof
namespace LogicLineages.PersistentMarking.AlphaCompletenessProof
open Spine NameBridge AlphaSizeProof

mutual
 theorem complete (a b : Term) (h : encode [] a = encode [] b) : Alpha a b := by
  cases a with
  | var σ x =>
    cases b with
    | var τ y =>
      simp only [encode, nameLookup, Expr.free.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact .refl
    | lam _ _ _ => cases h
    | head _ _ => cases h
    | marked _ _ _ _ => cases h
  | lam σ x body =>
    cases b with
    | var _ _ => cases h
    | head _ _ => cases h
    | marked _ _ _ _ => cases h
    | lam τ y other =>
      injection h with htype hb
      subst τ
      let z := max (max x y) (max (maxNamed body) (maxNamed other)) + 1
      have hzb : maxNamed body < z := by dsimp [z]; omega
      have hzo : maxNamed other < z := by dsimp [z]; omega
      have hzx : z ≠ x := by dsimp [z]; omega
      have hzy : z ≠ y := by dsimp [z]; omega
      have fb := aboveFresh σ z body hzb
      have fo := aboveFresh σ z other hzo
      have eb := OpeningBridgeProof.openingBridge σ x z body fb hzx
      have eo := OpeningBridgeProof.openingBridge σ y z other fo hzy
      have he : encode [] (renameFree (σ,x) (σ,z) body) =
          encode [] (renameFree (σ,y) (σ,z) other) :=
        eb.trans ((congrArg (openBody σ z) hb).trans eo.symm)
      have ih := complete (renameFree (σ,x) (σ,z) body) (renameFree (σ,y) (σ,z) other) he
      exact .trans (.rename fb hzx) (.trans (.lam ih) (.symm (.rename fo hzy)))
  | head f base =>
    cases b with
    | var _ _ => cases h
    | lam _ _ _ => cases h
    | marked _ _ _ _ => cases h
    | head g other =>
      injection h with hf hb
      subst g
      exact .head (completeArgs base other hb)
  | marked f τ base extras =>
    cases b with
    | var _ _ => cases h
    | lam _ _ _ => cases h
    | head _ _ => cases h
    | marked g υ other more =>
      injection h with hf ht hb he
      subst g
      subst υ
      exact .marked (completeArgs base other hb) (completeArgs extras more he)
 termination_by nodes a
 decreasing_by all_goals simp_wf; simp only [renameNodes, nodes, argsNodes]; omega
 theorem completeArgs (as bs : List Term) (h : encodeArgs [] as = encodeArgs [] bs) : AlphaArgs as bs := by
  cases as with
  | nil => cases bs with
    | nil => exact .nil
    | cons _ _ => cases h
  | cons a as =>
    cases bs with
    | nil => cases h
    | cons b bs =>
      injection h with ha hs
      exact .cons (complete a b ha) (completeArgs as bs hs)
 termination_by argsNodes as
 decreasing_by all_goals simp_wf; simp only [nodes, argsNodes]; omega
end

theorem alphaExact : BridgeTargets.AlphaExact := by
  intro a b
  exact ⟨fun h => AlphaEncodingProof.alphaEncode a b h [], complete a b⟩

theorem mapTypeAt (env : List Name) (i : Nat) (σ : Ty) (x : Nat)
    (h : env[i]? = some (σ,x)) : (env.map Prod.fst)[i]? = some σ := by
  cases env with
  | nil => simp at h
  | cons n ns =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst n
      rfl
    | succ i => exact mapTypeAt ns i σ x h
termination_by env.length

mutual
 theorem encodeScoped (env : List Name) (q : Term) : Scoped (env.map Prod.fst) (encode env q) := by
  cases q with
  | var σ x =>
    cases hl : nameLookup env (σ,x) with
    | none => simp [encode, hl, Scoped]
    | some i =>
      simp only [encode, hl, Scoped]
      exact mapTypeAt env i σ x (OpeningBridgeProof.lookupIndex env (σ,x) i hl).1
  | lam σ x body => exact encodeScoped ((σ,x)::env) body
  | head f base => exact encodeArgsScoped env base
  | marked f τ base extras => exact ⟨encodeArgsScoped env base, encodeArgsScoped env extras⟩
 termination_by sizeOf q
 theorem encodeArgsScoped (env : List Name) (qs : List Term) : ScopedArgs (env.map Prod.fst) (encodeArgs env qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨encodeScoped env q, encodeArgsScoped env qs⟩
 termination_by sizeOf qs
end

theorem decodeEncodeAlpha : BridgeTargets.DecodeEncodeAlpha := by
  intro a
  apply complete
  exact (DecodeRoundtripProof.encodeDecodeScoped (encode [] a) (encodeScoped [] a)).symm
end LogicLineages.PersistentMarking.AlphaCompletenessProof
