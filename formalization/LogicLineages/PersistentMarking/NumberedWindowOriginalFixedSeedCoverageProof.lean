import LogicLineages.PersistentMarking.NumberedWindowOwnCoverChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets

namespace LogicLineages.PersistentMarking.NumberedWindowOriginalFixedSeedCoverageProof
open NumberedWindowScalarAlgorithm (admitted vertices)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowOwnCoverChecks (exact_AdmittedOwnCover)

/-- At the actual finite source signature and type window, an admitted
seed belongs to its exact selected grammar cover. No assumption about
the lexical context or successful type decoding is needed. -/
theorem exact_FixedWindowSeedsCovered (S : Spine.Signature) (K : List Ty)
    (ctx : List Nat) (ty q : Nat) (h : admitted (fixed S K) ctx ty q = true) :
    q ∈ vertices (fixed S K) q := by
  simp only [admitted,Bool.and_eq_true] at h
  have raw := h.2
  obtain ⟨vs, hcover, hq⟩ := exact_AdmittedOwnCover S K q raw
  unfold vertices fixed
  rw [hcover]
  exact hq

#print axioms exact_FixedWindowSeedsCovered
end LogicLineages.PersistentMarking.NumberedWindowOriginalFixedSeedCoverageProof
