module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericContextProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericThinNextProof
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm (next context tick RawRoot)
open NumberedWindowRawApplicationLift (lift)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (FrameReport)
open NumberedWindowInternalSparseRawFunctionFrameNumericContextProof (contextFive)

private theorem actualNext (q r w f child g : Nat)
    (h : next 5 [w] q r = some (f,child,g)) :
    child = w ∧ ∃ d t a, unpackNode q = some (6,[d,t,f,a]) ∧
      unpackNode r = some (6,[d,t,g,a]) := by
  cases hq : unpackNode q with
  | none => simp [next,hq] at h
  | some lhs =>
    cases hr : unpackNode r with
    | none => simp [next,hq,hr] at h
    | some rhs =>
      simp only [next,hq,hr] at h
      obtain ⟨same,d,t,a,hs,ht⟩ := contextFive lhs rhs w f child g h
      exact ⟨same,d,t,a,by first | exact congrArg some hs | exact hq.trans (congrArg some hs),
        by first | exact congrArg some ht | exact hr.trans (congrArg some ht)⟩

theorem nextReports (q w r f child g : Nat) :
    tagFiveNext q w r = some (f,child,g) ↔ FrameReport q w r f child g := by
  constructor
  · intro h
    cases hw : unpackNode w with
    | none => simp [tagFiveNext,hw] at h
    | some node =>
      rcases node with ⟨tag,fields⟩
      rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
        rcases fields with _ | ⟨w',_ | ⟨later,rest⟩⟩ <;>
        simp [tagFiveNext,hw] at h
      obtain ⟨same,d,t,a,hq,hr⟩ := actualNext q r w' f child g h
      rw [same]
      exact ⟨d,t,a,by first | exact hw | rfl,hq,hr⟩
  · rintro ⟨d,t,a,hw,hq,hr⟩
    simp [tagFiveNext,hw,next,hq,hr,context]

theorem literalTick (root : RawRoot) (status : Bool) (dom cod arg src child dst : Nat) :
    tick root (status,some (lift dom cod arg src child dst)) =
      (false,some (src,child,dst)) := by
  simp [lift,tick,next,context,nodePacked]

theorem literalNext (dom cod arg src child dst : Nat) :
    let out := lift dom cod arg src child dst
    tagFiveNext out.1 out.2.1 out.2.2 = some (src,child,dst) := by
  apply (nextReports _ _ _ src child dst).mpr
  exact ⟨dom,cod,arg,nodePacked 5 [child],nodePacked 6 [dom,cod,src,arg],
    nodePacked 6 [dom,cod,dst,arg]⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericThinNextProof
