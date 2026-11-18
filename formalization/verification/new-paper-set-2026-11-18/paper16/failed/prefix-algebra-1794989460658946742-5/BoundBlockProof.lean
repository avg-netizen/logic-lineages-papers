import LogicLineages.PersistentMarking.PrefixEscapeSupportTargets
import LogicLineages.PersistentMarking.RefinementFreeBlockProof
import LogicLineages.PersistentMarking.FreeShiftProof
namespace LogicLineages.PersistentMarking.BoundBlockProof
open Spine RefinementFreeBlockProof

theorem bound (inner outer : Args) (d : Nat) (σ : Ty) (i : Nat) :
    substitute inner d (substitute outer (d+inner.length) (.bound σ i)) =
      substitute (inner.append outer) d (.bound σ i) := by
  by_cases hlo : i < d
  · have hfirst : i < d+inner.length := by omega
    simp [substitute,hlo,hfirst]
  · by_cases hin : i < d+inner.length
    · have hi : i-d < inner.length := by omega
      obtain ⟨v,hv⟩ := getInside inner (i-d) hi
      simp only [substitute,hin,if_true,hlo,if_false,hv,appendGet,hi]
    · have hi : ¬ i-d < inner.length := by omega
      have hidx : i-d-inner.length = i-(d+inner.length) := by omega
      cases ho : outer.get (i-(d+inner.length)) with
      | some v =>
        simp only [substitute,hin,hlo,if_false,ho,appendGet,hi,hidx]
        simpa only [Nat.add_zero] using FreeShiftProof.cancellation inner d 0 v
      | none =>
        have hlen := InsertionProof.getNoneLength outer (i-(d+inner.length)) ho
        have hlo' : ¬ i-outer.length < d := by omega
        have hinner : inner.length ≤ i-outer.length-d := by omega
        simp only [substitute,hin,hlo,if_false,ho,hlo',getPast inner _ hinner,
          appendGet,hi,hidx,appendLength]
        congr 1
        omega

mutual
 theorem block (inner outer : Args) (d : Nat) (q : Expr) :
    substitute inner d (substitute outer (d+inner.length) q) = substitute (inner.append outer) d q := by
  cases q with
  | free σ x => rfl
  | bound σ i => exact bound inner outer d σ i
  | lam σ q =>
    have he : d+inner.length+1 = (d+1)+inner.length := by omega
    simp only [substitute,he,block inner outer (d+1) q]
  | head f qs => simp only [substitute,blockArgs inner outer d qs]
  | marked f τ qs es => simp only [substitute,blockArgs inner outer d qs,blockArgs inner outer d es]
 termination_by sizeOf q
 theorem blockArgs (inner outer : Args) (d : Nat) (qs : Args) :
    substituteArgs inner d (substituteArgs outer (d+inner.length) qs) = substituteArgs (inner.append outer) d qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [substituteArgs,block inner outer d q,blockArgs inner outer d qs]
 termination_by sizeOf qs
end

theorem blockComposition : PrefixEscapeSupportTargets.BlockComposition := block
theorem blockArgsComposition : PrefixEscapeSupportTargets.BlockArgsComposition := blockArgs
end LogicLineages.PersistentMarking.BoundBlockProof
