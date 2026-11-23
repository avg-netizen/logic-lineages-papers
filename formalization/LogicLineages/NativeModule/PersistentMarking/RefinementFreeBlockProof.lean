module

public import LogicLineages.NativeModule.PersistentMarking.RefinementFullCallTargets
public import LogicLineages.NativeModule.PersistentMarking.InsertionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementFreeBlockProof
open Spine

theorem getPast (vs : Args) (i : Nat) (h : vs.length ≤ i) : vs.get i = none := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    cases i with
    | zero => simp [Args.length] at h
    | succ i => exact getPast vs i (by simp only [Args.length] at h; omega)
termination_by sizeOf vs

theorem getInside (vs : Args) (i : Nat) (h : i < vs.length) : ∃ v, vs.get i = some v := by
  cases vs with
  | nil => simp [Args.length] at h
  | cons v vs =>
    cases i with
    | zero => exact ⟨v,rfl⟩
    | succ i => exact getInside vs i (by simp only [Args.length] at h; omega)
termination_by sizeOf vs

theorem appendLength (vs ws : Args) : (vs.append ws).length = vs.length + ws.length := by
  cases vs with
  | nil => simp [Args.append,Args.length]
  | cons v vs => simp only [Args.append,Args.length,appendLength vs ws]; omega
termination_by sizeOf vs

theorem appendGet (vs ws : Args) (i : Nat) :
    (vs.append ws).get i = if i < vs.length then vs.get i else ws.get (i-vs.length) := by
  cases vs with
  | nil => simp [Args.append,Args.length]
  | cons v vs =>
    cases i with
    | zero => simp [Args.append,Args.length,Args.get]
    | succ i =>
      simp only [Args.append,Args.get,appendGet vs ws i,Args.length]
      have hlt : (i+1 < 1+vs.length) ↔ i < vs.length := by omega
      have hsub : i+1-(1+vs.length) = i-vs.length := by omega
      simp only [hlt,hsub]
termination_by sizeOf vs

theorem bound (vs : Args) (d : Nat) (σ : Ty) (x : Nat) (τ : Ty) (i : Nat) :
    substitute vs d (substitute (.cons (.free σ x) .nil) (d+vs.length) (.bound τ i)) =
    substitute (vs.append (.cons (.free σ x) .nil)) d (.bound τ i) := by
  by_cases hlo : i < d
  · have hfirst : i < d+vs.length := by omega
    simp [substitute,hlo,hfirst]
  · by_cases hin : i < d+vs.length
    · have hi : i-d < vs.length := by omega
      obtain ⟨v,hv⟩ := getInside vs (i-d) hi
      simp only [substitute,hin,if_true,hlo,if_false,hv,appendGet,hi]
    · by_cases heq : i = d+vs.length
      · subst i
        have hi : ¬ d+vs.length < d := by omega
        simp [substitute,hi,Args.get,shift,appendGet,appendLength,Args.length]
      · have hout : d+vs.length < i := by omega
        have hi' : ¬ i-1 < d := by omega
        have hp : vs.length ≤ i-1-d := by omega
        have hp' : ¬ i-d < vs.length := by omega
        have hg : (Args.cons (.free σ x) .nil).get (i-(d+vs.length)) = none := getPast _ _ (by simp only [Args.length]; omega)
        have hg' : (Args.cons (.free σ x) .nil).get (i-d-vs.length) = none := getPast _ _ (by simp only [Args.length]; omega)
        simp only [substitute,hin,if_false,hg,Args.length,hi',hlo,
          getPast vs (i-1-d) hp,appendGet,hp',hg',appendLength]
        congr 1
        omega

mutual
 theorem block (vs : Args) (d : Nat) (σ : Ty) (x : Nat) (q : Expr) :
    substitute vs d (substitute (.cons (.free σ x) .nil) (d+vs.length) q) =
    substitute (vs.append (.cons (.free σ x) .nil)) d q := by
  cases q with
  | free τ y => rfl
  | bound τ i => exact bound vs d σ x τ i
  | lam τ q =>
    have he : d+vs.length+1 = (d+1)+vs.length := by omega
    simp only [substitute,he,block vs (d+1) σ x q]
  | head f qs => simp only [substitute,blockArgs vs d σ x qs]
  | marked f τ qs es => simp only [substitute,blockArgs vs d σ x qs,blockArgs vs d σ x es]
 termination_by sizeOf q
 theorem blockArgs (vs : Args) (d : Nat) (σ : Ty) (x : Nat) (qs : Args) :
    substituteArgs vs d (substituteArgs (.cons (.free σ x) .nil) (d+vs.length) qs) =
    substituteArgs (vs.append (.cons (.free σ x) .nil)) d qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [substituteArgs,block vs d σ x q,blockArgs vs d σ x qs]
 termination_by sizeOf qs
end

theorem freeOuterBlock : RefinementFullCallTargets.FreeOuterBlock := block
theorem freeOuterBlockArgs : RefinementFullCallTargets.FreeOuterBlockArgs := blockArgs
end LogicLineages.PersistentMarking.RefinementFreeBlockProof
