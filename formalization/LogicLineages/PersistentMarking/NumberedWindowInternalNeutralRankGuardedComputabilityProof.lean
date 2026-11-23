module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankedNeutralTypeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankBareProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankAccessibilityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDropProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardedComputabilityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open LogicLineages.OrdinalComparison.Source (Ty)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalRankedNeutralTypeProof (exact_RankedNeutralComputability)
open NumberedWindowInternalNeutralRankGuard (rankEven rankApplication)
open NumberedWindowInternalNeutralRankGuardApplicationProof (exact_OpenRankGuardedApplication)
open NumberedWindowInternalNeutralRankGuardDropProof (exact_OpenRankGuardDrop)
open NumberedWindowInternalNeutralRankAccessibilityProof (exact_OpenRankAccessibility)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalNeutralAddressRankBareProof (exact_OpenAddressRankBareFree exact_OpenAddressRankBareBottom)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)

/-- All finite types in the exact same physically rank-guarded object
body. The real rank report gives membership at base; actual guarded
application pays the recursive arrow step for the actual y. No oracle for
C or I and no meta-to-object numeric reflection. -/
theorem exact_OpenRankGuardedComputability (i j g : Program 1) (r d p : Program 3) (c : Nat) :
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (k q : OTerm α),
      let S := data i j (rankEven i g r) d
      let B := sourceBody S c
      Nonempty (Derivation B Γ (unary g (suc k) q)) →
      Nonempty (Derivation B Γ (carrier S false c q)) →
      Nonempty (Derivation B Γ (formula (rankApplication i g p) τ q)) := by
  let S := data i j (rankEven i g r) d
  refine exact_RankedNeutralComputability S g (rankApplication i g p) c ?_
    (exact_OpenRankGuardedApplication i j g (rankEven i g r) d p c)
  intro α Γ k q ranked carried
  exact exact_OpenRankAccessibility (exact_OpenRankGuardDrop i j g r d c) k q carried ranked

/-- The actual bare pattern emits a rank report at every requested
finite type. Its true scalar carrier remains explicit. The numerical
calibration of the whole guarded pair is a separate theorem. -/
theorem exact_OpenRankGuardedBareFreeC (i j raw : Program 1) (r d p : Program 3)
    (c : Nat) (τ : Ty) (α : Type) (Γ : List (Formula α)) (q ctx ty name : OTerm α) :
    let g := addressRank raw
    let S := data i j (rankEven i g r) d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (equal q (packedFreeTerm ctx ty name))) →
    Nonempty (Derivation B Γ (carrier S false c q)) →
    Nonempty (Derivation B Γ (formula (rankApplication i g p) τ q)) := by
  intro g S B shape carried
  exact exact_OpenRankGuardedComputability i j g r d p c τ α Γ (suc z) q
    (exact_OpenAddressRankBareFree raw q ctx ty name shape) carried

theorem exact_OpenRankGuardedBareBottomC (i j raw : Program 1) (r d p : Program 3)
    (c : Nat) (τ : Ty) (α : Type) (Γ : List (Formula α)) (q ctx ty : OTerm α) :
    let g := addressRank raw
    let S := data i j (rankEven i g r) d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (equal q (packedBottomTerm ctx ty))) →
    Nonempty (Derivation B Γ (carrier S false c q)) →
    Nonempty (Derivation B Γ (formula (rankApplication i g p) τ q)) := by
  intro g S B shape carried
  exact exact_OpenRankGuardedComputability i j g r d p c τ α Γ z q
    (exact_OpenAddressRankBareBottom raw q ctx ty shape) carried

#print axioms exact_OpenRankGuardedComputability
#print axioms exact_OpenRankGuardedBareFreeC
#print axioms exact_OpenRankGuardedBareBottomC
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardedComputabilityProof
