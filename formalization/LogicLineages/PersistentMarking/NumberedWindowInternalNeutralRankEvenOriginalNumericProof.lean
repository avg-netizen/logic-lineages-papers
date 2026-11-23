module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpinePositiveRankProof
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsScalarProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankEvenOriginalNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar least)
open NumberedWindowConcreteCheckers (step positive)
open NumberedWindowPositivePathAlgorithm (addressRS)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowConcretePositiveEndpointsScalarProof (scalarEndpoints)
open NumberedWindowNeutralSpinePositiveRankProof (KeepsNeutralRank exact_OriginalNeutralRankPositive)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralAddressRankNumericProof (exact_OriginalAddressNeutralRank)
open NumberedWindowInternalNeutralRankGuard (rankEven)
open NumberedWindowInternalNeutralRankGuardNumericProof (exact_RankEvenNumeric)

/-- An original positive tape whose actual source ranks is carried and
strictly decreases in the same physical numeric rank. The only unsupplied
arithmetic dependency here is preservation across actual exchange. -/
theorem exact_OriginalRankedAddressPositive (xs : Entries) (s : Settings)
    (pres : KeepsNeutralRank s) (i raw : Program 1)
    (scalarFit : ∀ y, run i y = (scalar s y).toNat)
    (rankFit : ∀ q, run raw q = rawRank q)
    (x w y : Nat) (accepted : positive xs s x w y = true) (live : run (addressRank raw) x ≠ 0) :
    run (addressRank raw) y ≠ 0 ∧ run (addressRank raw) y < run (addressRank raw) x ∧ run i y = 1 := by
  have targetScalar : run i y = 1 := by
    rw [scalarFit,(scalarEndpoints xs s x w y accepted).2]
    rfl
  change addressRS (step xs s) (least s) x w y = true at accepted
  unfold addressRS at accepted
  cases reads : addressView x with
  | none => simp [reads] at accepted
  | some src =>
    obtain ⟨ctx,ty,source⟩ := src
    cases readt : addressView y with
    | none => simp [reads,readt] at accepted
    | some dest =>
      obtain ⟨ctx',ty',target⟩ := dest
      have reports : ctx = ctx' ∧ ty = ty' ∧
          NumberedWindowPositivePathAlgorithm.positive (step xs s) (least s) ctx ty source w target = true := by
        simpa [reads,readt,Bool.and_eq_true,beq_iff_eq,and_assoc] using accepted
      obtain ⟨sameCtx,sameTy,path⟩ := reports
      subst ctx'
      subst ty'
      have actualSource := exact_OriginalAddressNeutralRank raw rankFit x ctx ty source reads
      have actualTarget := exact_OriginalAddressNeutralRank raw rankFit y ctx ty target readt
      have descent := exact_OriginalNeutralRankPositive xs s pres ctx ty source w target
        (actualSource ▸ live) path
      exact ⟨actualTarget.symm ▸ descent.1, by rw [actualTarget,actualSource]; exact descent.2, targetScalar⟩

theorem exact_OriginalRankEvenAllInputs (xs : Entries) (s : Settings) (pres : KeepsNeutralRank s)
    (i raw : Program 1) (r : Program 3)
    (scalarFit : ∀ y, run i y = (scalar s y).toNat)
    (rankFit : ∀ q, run raw q = rawRank q)
    (old : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) :
    ∀ x w y, evaluate (rankEven i (addressRank raw) r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      (positive xs s x w y).toNat :=
  exact_RankEvenNumeric i (addressRank raw) r (positive xs s) old
    (exact_OriginalRankedAddressPositive xs s pres i raw scalarFit rankFit)

#print axioms exact_OriginalRankedAddressPositive
#print axioms exact_OriginalRankEvenAllInputs
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankEvenOriginalNumericProof
