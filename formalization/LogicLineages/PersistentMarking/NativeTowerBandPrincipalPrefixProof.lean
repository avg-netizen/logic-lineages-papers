import LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandImageRelIsoProof

namespace LogicLineages.PersistentMarking.NativeTowerBandPrincipalPrefixProof
open NativeTowerNestedInnerOrbitLexProof NativeTowerVariableDimensionBandsProof
open NativeTowerVariableDimensionBandImageRelIsoProof
open Spine NativeIteratorStrictTargets NativeTowerWitnessFamilyProof

/-- Lexically least coordinates in each actual positive-dimensional band. -/
def leastCoords : (d : Nat) → OrbitCoords d
  | 0 => (0 : Nat)
  | d+1 => (leastCoords d,0)

def firstBandPoint (d : Nat) : BandCoords := ⟨d,leastCoords d⟩

theorem nothingBelowLeast (d : Nat) (p : OrbitCoords d) : ¬ OrbitLex d p (leastCoords d) := by
  induction d with
  | zero =>
    simp [OrbitLex,leastCoords]
  | succ d ih =>
    intro h
    change OrbitLex d p.1 (leastCoords d) ∨ (p.1 = leastCoords d ∧ p.2 < 0) at h
    rcases h with h | ⟨_,h⟩
    · exact ih p.1 h
    · exact Nat.not_lt_zero p.2 h

theorem exact_OriginalBandPrincipalPrefix (p : BandCoords) (d : Nat) :
    BandLex p (firstBandPoint d) ↔ p.1 < d := by
  rcases p with ⟨k,p⟩
  change (k < d ∨ ∃ same : k = d, OrbitLex k p (cast (congrArg OrbitCoords same.symm) (leastCoords d))) ↔ k < d
  constructor
  · rintro (earlier | ⟨e,h⟩)
    · exact earlier
    · subst k
      exact (nothingBelowLeast d p h).elim
  · exact Or.inl

/-- The same initial segment is witnessed inside the actual fixed tower image.
It is not a claim about all native indices below this point. -/
theorem exact_ActualBandImagePrincipalPrefix (S : Signature) (l d : Nat) (p : BandCoords) :
    actualBandStrict S l (actualBandRelIso S l p) (actualBandRelIso S l (firstBandPoint d)) ↔ p.1 < d :=
  ((actualBandRelIso S l).map_rel_iff).trans (exact_OriginalBandPrincipalPrefix p d)

theorem exact_OriginalBandStartsCofinal (p : BandCoords) :
    ∃ d, BandLex p (firstBandPoint d) :=
  ⟨p.1+1,(exact_OriginalBandPrincipalPrefix p (p.1+1)).2 (Nat.lt_succ_self _)⟩

#print axioms exact_OriginalBandPrincipalPrefix
#print axioms exact_ActualBandImagePrincipalPrefix
#print axioms exact_OriginalBandStartsCofinal
end LogicLineages.PersistentMarking.NativeTowerBandPrincipalPrefixProof
