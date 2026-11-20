module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericNextProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericChecks
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (value guardBit tape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (guardReports termFields witnessField)
open NumberedWindowInternalSparseRawFunctionFrameNumericNextProof (nextReports literalTick literalNext)
open NumberedWindowRawApplicationLift (lift)

theorem exact_AllRawFunctionFrame : ExactAllRawFunctionFrame := by
  intro q w r
  rw [value]
  cases h : tagFiveNext q w r with
  | none =>
    rcases guardBit (tape q w r) with no | yes
    · simp only [no,if_pos,encodeFrame]
    · obtain ⟨f,child,g,fields⟩ := (guardReports q w r).mp yes
      have impossible := (nextReports q w r f child g).mpr fields
      rw [h] at impossible
      cases impossible
  | some out =>
    rcases out with ⟨f,child,g⟩
    have fields := (nextReports q w r f child g).mp h
    have yes := (guardReports q w r).mpr ⟨f,child,g,fields⟩
    obtain ⟨d,t,a,hw,hq,hr⟩ := fields
    have w0 := witnessField hw
    have q2 := (termFields hq).2.2.1
    have r2 := (termFields hr).2.2.1
    simp [yes,w0,q2,r2]

theorem exact_LiteralFunctionFrame : ExactLiteralFunctionFrame := by
  intro root status dom cod arg src child dst
  let out := lift dom cod arg src child dst
  refine ⟨literalTick root status dom cod arg src child dst,?_⟩
  rw [exact_AllRawFunctionFrame]
  exact congrArg encodeFrame (literalNext dom cod arg src child dst)

#print axioms exact_AllRawFunctionFrame
#print axioms exact_LiteralFunctionFrame
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericChecks
