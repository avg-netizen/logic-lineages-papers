module
public import LogicLineages.OrdinalComparison.CubicLeaderRecognitionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CubicLeaderRecognition.Targets
open CounterLeaderExpansion

/-- The unchanged cubic specialization of the accepted principal modulus and
actual pair recognition. No injectivity, strict-mass or comparator premise. -/
def ActualCubicPairRecognition : Prop :=
  (∀ c e : Nat, cubicModulus c e =
    encodedPrincipalKernelMassModulus (rawNoteEncode (ONote.ofNat 3)) c e) ∧
  (∀ c e t u : Nat, cubicModulus c e ≤ t → cubicModulus c e ≤ u →
    (kernel 3 c t = kernel 3 e u ↔ c = e ∧ t = u))

/-- Actual leaders may come from different ranks. Equality recognizes the
original prefix mass and actual cubic bottom input, while both higher entry
chains remain on their explicit original genuine-domain tails. This does not
identify higher-rank original inputs or prove cross-rank collision sums. -/
def ActualLeaderRecognition : Prop := ∀ n m c e t u : Nat,
  leaderTail n c e ≤ t → leaderTail m e c ≤ u →
  (leader n c t = leader m e u ↔
    c = e ∧ bottomInput n c t = bottomInput m e u)

end LogicLineages.OrdinalComparison.CubicLeaderRecognition.Targets
