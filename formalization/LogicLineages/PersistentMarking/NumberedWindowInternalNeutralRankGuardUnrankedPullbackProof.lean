module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralUnrankedPullbackProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDropProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardUnrankedPullbackProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalPullbackTargets (Pullback)
open NumberedWindowInternalNeutralRankGuard (rankEven rankApplication)
open NumberedWindowInternalNeutralRankGuardDropProof (exact_OpenRankGuardDrop)
open NumberedWindowInternalNeutralUnrankedPullbackTargets (UnrankedForwardRule)
open NumberedWindowInternalNeutralUnrankedPullbackProof (exact_InternalUnrankedPullback)

/-- Physical rank callback discharges the ranked branch. The only
function-path image input is for a held rank-zero source. -/
theorem exact_RankGuardUnrankedPullback (i j g : Program 1) (r d p : Program 3) (c : Nat)
    (guards : InputGuards i j (rankEven i g r) d (rankApplication i g p))
    (forward : UnrankedForwardRule (data i j (rankEven i g r) d) g (rankApplication i g p) c) :
    Pullback (data i j (rankEven i g r) d) (rankApplication i g p) c :=
  exact_InternalUnrankedPullback i j g (rankEven i g r) d (rankApplication i g p) c
    guards (exact_OpenRankGuardDrop i j g r d c) forward

#print axioms exact_RankGuardUnrankedPullback
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardUnrankedPullbackProof
