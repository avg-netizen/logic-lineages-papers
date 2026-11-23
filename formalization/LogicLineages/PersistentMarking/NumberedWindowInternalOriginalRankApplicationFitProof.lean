module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankNumericProof
import LogicLineages.PersistentMarking.NumberedWindowOriginalApplicationRawRankProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankApplicationFitProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressApplication (graph)
open NumberedWindowScalarAlgorithm (Settings scalar edge)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralAddressRankNumericProof (exact_OriginalAddressNeutralRank)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowInternalNeutralRankGuardNumericProof (exact_RankApplicationNumeric)
open NumberedWindowOriginalApplicationRawRankProof
  (exact_OriginalApplicationRawRank exact_OriginalApplicationFunctionAddress)
open NumberedWindowInternalSparsePathEnvelope (run)

theorem exact_OriginalAddressRankApplicationReport (s : Settings) (raw : Program 1)
    (rawFit : ∀ k, run raw k = rawRank k)
    (transport : ∀ ctx t a b, edge s ctx t a b = true → rawRank b = rawRank a)
    (f u y : Nat) (accepted : graph s f u y = true)
    (carrier : scalar s y = true) (pos : run (addressRank raw) f ≠ 0) :
    run (addressRank raw) y = run (addressRank raw) f + 1 := by
  obtain ⟨ctx,ty,fn,hf⟩ := exact_OriginalApplicationFunctionAddress s f u y accepted
  have rankF := exact_OriginalAddressNeutralRank raw rawFit f ctx ty fn hf
  have nonzero : rawRank fn ≠ 0 := by rw [← rankF]; exact pos
  obtain ⟨outCtx,outTy,k,hy,plus⟩ :=
    exact_OriginalApplicationRawRank s f u y fn ty ctx transport hf accepted carrier nonzero
  have rankY := exact_OriginalAddressNeutralRank raw rawFit y outCtx outTy k hy
  calc
    run (addressRank raw) y = rawRank k := rankY
    _ = rawRank fn + 1 := plus
    _ = run (addressRank raw) f + 1 := congrArg (· + 1) rankF.symm

/-- Exact physical ranked p, conditional only on the actual raw edge
invariant and actual original output-scalar law, plus physical fits. -/
theorem exact_OriginalRankedApplicationFit (s : Settings) (i raw : Program 1) (p : Program 3)
    (iFit : ∀ y, run i y = (scalar s y).toNat)
    (rawFit : ∀ k, run raw k = rawRank k)
    (pFit : ∀ f u y, evaluate p (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (graph s f u y).toNat)
    (transport : ∀ ctx t a b, edge s ctx t a b = true → rawRank b = rawRank a)
    (scalarOutput : ∀ f u y, graph s f u y = true → scalar s y = true) :
    ∀ f u y, evaluate (rankApplication i (addressRank raw) p) (f ::ᵥ u ::ᵥ y ::ᵥ nil) =
      (graph s f u y).toNat := by
  have holds : ∀ f u y, graph s f u y = true → run (addressRank raw) f ≠ 0 →
      run (addressRank raw) y ≠ 0 ∧ run i y = 1 := by
    intro f u y accepted pos
    have carrier := scalarOutput f u y accepted
    have plus := exact_OriginalAddressRankApplicationReport s raw rawFit transport f u y accepted carrier pos
    exact ⟨fun bad => Nat.succ_ne_zero _ (plus.symm.trans bad),
      (iFit y).trans (congrArg Bool.toNat carrier)⟩
  exact exact_RankApplicationNumeric i (addressRank raw) p (graph s) pFit holds

#print axioms exact_OriginalAddressRankApplicationReport
#print axioms exact_OriginalRankedApplicationFit
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRankApplicationFitProof
