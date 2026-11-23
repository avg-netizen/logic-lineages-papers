module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsTargets
import LogicLineages.PersistentMarking.NumberedWindowConcretePositiveEndpointsHopProof
import LogicLineages.PersistentMarking.NumberedWindowOriginalLeastFeatureProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpinePositiveRankProof
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankCalibrationProof
  (exact_RawNeutralShapeFromRank exact_RawNeutralRankFromShape)
open NumberedWindowNeutralSpineRawRankProof (exact_OriginalNeutralSpineStepRank)
open NumberedWindowOriginalLeastFeatureProof (exact_OriginalLeastPreservesFeature)
open NumberedWindowConcretePositiveEndpointsHopProof (hopReport)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings edge vertices least)
open NumberedWindowConcreteCheckers (step)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowPositivePathAlgorithm (advance positive walk)

/-- The only remaining conservation premise for selected classes:
the actual original directed exchange keeps the raw left rank. -/
def KeepsNeutralRank (s : Settings) : Prop :=
  ∀ ctx ty a b, edge s ctx ty a b = true → rawRank b = rawRank a

theorem exact_OriginalNeutralRankLeast (s : Settings) (pres : KeepsNeutralRank s)
    (ctx : List Nat) (ty q y : Nat) (call : least s ctx ty q = some y) :
    rawRank y = rawRank q :=
  exact_OriginalLeastPreservesFeature (edge s ctx ty) (vertices s q) q y rawRank (pres ctx ty) call

/-- Preserve the exact hop accepted by the original advance evaluator.
The original raw child descends, and both selected endpoint ranks are
the true raw ranks by the stated real exchange law. -/
theorem exact_OriginalNeutralRankAdvance (xs : Entries) (s : Settings) (pres : KeepsNeutralRank s)
    (ctx : List Nat) (ty src code dst : Nat) (live : rawRank src ≠ 0)
    (accepted : advance (step xs s ctx ty) (least s ctx ty) (some src) code = some dst) :
    rawRank dst ≠ 0 ∧ rawRank dst < rawRank src := by
  obtain ⟨q,w,y,_,real,_,_,startCall,endCall⟩ := hopReport xs s ctx ty src code dst accepted
  have l := exact_OriginalNeutralRankLeast s pres ctx ty q src startCall
  have r := exact_OriginalNeutralRankLeast s pres ctx ty y dst endCall
  have source : rawRank q ≠ 0 := l ▸ live
  obtain ⟨n,ranked⟩ : ∃ n, rawRank q = n+1 := by
    cases h : rawRank q with
    | zero => exact False.elim (source h)
    | succ n => exact ⟨n,rfl⟩
  have shape := exact_RawNeutralShapeFromRank q n ranked
  obtain ⟨_,m,target,smaller⟩ := exact_OriginalNeutralSpineStepRank xs s ctx ty q w y n shape real
  have last := exact_RawNeutralRankFromShape target
  rw [l,ranked,r,last]
  exact ⟨Nat.succ_ne_zero m,Nat.succ_lt_succ smaller⟩

private theorem noRestart (f : Nat → Nat → Nat → Bool) (L : Nat → Option Nat)
    (codes : List Nat) : codes.foldl (advance f L) none = none := by
  induction codes with
  | nil => rfl
  | cons q qs ih => exact ih

private theorem finishRank (xs : Entries) (s : Settings) (pres : KeepsNeutralRank s)
    (ctx : List Nat) (ty : Nat) (codes : List Nat) :
    ∀ src dst, rawRank src ≠ 0 →
      codes.foldl (advance (step xs s ctx ty) (least s ctx ty)) (some src) = some dst →
      rawRank dst ≠ 0 ∧ rawRank dst ≤ rawRank src := by
  induction codes with
  | nil =>
    intro src dst hs eq
    have same : src = dst := Option.some.inj eq
    subst dst
    exact ⟨hs,Nat.le_refl _⟩
  | cons first rest ih =>
    intro src dst hs eq
    rw [List.foldl_cons] at eq
    cases result : advance (step xs s ctx ty) (least s ctx ty) (some src) first with
    | none =>
      rw [result,noRestart] at eq
      cases eq
    | some mid =>
      have head := exact_OriginalNeutralRankAdvance xs s pres ctx ty src first mid hs result
      rw [result] at eq
      have tail := ih mid dst head.1 eq
      exact ⟨tail.1,Nat.le_trans tail.2 (Nat.le_of_lt head.2)⟩

/-- The complete nonempty original positive checker strictly lowers
neutral rank. All path rows are those decoded from the very same
certificate; no class or witness is replaced. -/
theorem exact_OriginalNeutralRankPositive (xs : Entries) (s : Settings) (pres : KeepsNeutralRank s)
    (ctx : List Nat) (ty src cert dst : Nat) (live : rawRank src ≠ 0)
    (accepted : positive (step xs s) (least s) ctx ty src cert dst = true) :
    rawRank dst ≠ 0 ∧ rawRank dst < rawRank src := by
  cases seen : unpack cert with
  | none => simp [positive,seen] at accepted
  | some codes =>
    cases codes with
    | nil => simp [positive,seen] at accepted
    | cons first rest =>
      have folded : (first::rest).foldl (advance (step xs s ctx ty) (least s ctx ty))
          (some src) = some dst := by
        simpa [positive,walk,seen,beq_iff_eq] using accepted
      rw [List.foldl_cons] at folded
      cases result : advance (step xs s ctx ty) (least s ctx ty) (some src) first with
      | none =>
        rw [result,noRestart] at folded
        cases folded
      | some mid =>
        have head := exact_OriginalNeutralRankAdvance xs s pres ctx ty src first mid live result
        rw [result] at folded
        have tail := finishRank xs s pres ctx ty rest mid dst head.1 folded
        exact ⟨tail.1,Nat.lt_of_le_of_lt tail.2 head.2⟩

#print axioms exact_OriginalNeutralRankLeast
#print axioms exact_OriginalNeutralRankAdvance
#print axioms exact_OriginalNeutralRankPositive
end LogicLineages.PersistentMarking.NumberedWindowNeutralSpinePositiveRankProof
