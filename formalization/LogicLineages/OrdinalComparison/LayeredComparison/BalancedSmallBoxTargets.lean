module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Targets
open BalancedSyntax

/-- Agreement on the ORIGINAL ambient support preserves actual source values
and the ordered list of ALL original complete inputs. The whole shared basis
is also stable if any atom occurs; no claim is made about unused basis names
in the head-free case. No positivity or genuine-head premise is needed. -/
def ActualSourceSupportStability : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k :: Γ)) (E F : Upper k) (ν μ : Nat → Nat),
  (∀ i ∈ sourceAmbient k Γ C E F, ν i = μ i) →
  value (k :: Γ) C E ν = value (k :: Γ) C E μ ∧
  value (k :: Γ) C F ν = value (k :: Γ) C F μ ∧
  completeInputs k Γ C E F ν = completeInputs k Γ C E F μ ∧
  ((comparisonRow E F).atoms ≠ [] → basisValues k Γ C ν = basisValues k Γ C μ)

/-- One small ORIGINAL complete input bounds the whole basis sum, every
basis value and every raw name in either the basis or original pair support
by the ORIGINAL L. Genuine lower-certificate expressions supply actual
support domination. The top-level heads need no additional validity premise,
and even positivity of the raw valuation is unnecessary for these bounds. -/
def ActualSmallInputBounds : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k :: Γ)) (E F : Upper k) (ν : Nat → Nat),
  genuineCertificate (k :: Γ) C → smallBranch k Γ C E F ν →
  (basisValues k Γ C ν).sum < originalThreshold E F ∧
  (∀ j : Fin k, value Γ C.1 (C.2 j) ν < originalThreshold E F) ∧
  (∀ i ∈ basisSupport k Γ C, ν i < originalThreshold E F) ∧
  (∀ i ∈ sourceAmbient k Γ C E F, ν i < originalThreshold E F)

/-- The accepted words/lookup are reused, with their exact positive-coordinate
membership, empty-support singleton, canonical map agreement, outside-one
default and positive bounded representatives. No source evaluator or numeric
computability claim is included in these elementary finite-list laws. -/
def ExactFiniteBox : Prop :=
  (∀ (L n : Nat) (word : List Nat),
    word ∈ singleCoreBoxWords L n ↔
      word.length = n ∧ ∀ v ∈ word, 0 < v ∧ v < L) ∧
  (∀ L : Nat, singleCoreBoxWords L 0 = [[]]) ∧
  (∀ (support : List Nat) (ν : Nat → Nat),
    ∀ i ∈ support, singleCoreBoxLookup support (support.map ν) i = ν i) ∧
  (∀ (support word : List Nat), word.length = support.length →
    ∀ i, i ∉ support → singleCoreBoxLookup support word i = 1) ∧
  (∀ (L : Nat) (support word : List Nat),
    word ∈ singleCoreBoxWords L support.length →
    (∀ i, 0 < singleCoreBoxLookup support word i) ∧
    (∀ i ∈ support, singleCoreBoxLookup support word i < L))

/-- Every ambient-positive small-branch valuation has its exact finite word
at the ORIGINAL threshold, with identical source values and ALL original
complete inputs. Outside raw coordinates of ν have no premise at all. Their
replacement by one is justified only by actual-support stability. -/
def ExactSmallBranchRepresentative : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k :: Γ)) (E F : Upper k) (ν : Nat → Nat),
  genuineCertificate (k :: Γ) C →
  positiveOn (sourceAmbient k Γ C E F) ν → smallBranch k Γ C E F ν →
  ∃ word : List Nat,
    word = (sourceSupport k Γ C E F).map ν ∧
    word ∈ singleCoreBoxWords (BalancedRow.threshold (comparisonRow E F))
      (sourceSupport k Γ C E F).length ∧
    (∀ i ∈ sourceAmbient k Γ C E F, boxValuation k Γ C E F word i = ν i) ∧
    (∀ i, 0 < boxValuation k Γ C E F word i) ∧
    (∀ i, i ∉ sourceAmbient k Γ C E F → boxValuation k Γ C E F word i = 1) ∧
    value (k :: Γ) C E (boxValuation k Γ C E F word) = value (k :: Γ) C E ν ∧
    value (k :: Γ) C F (boxValuation k Γ C E F word) = value (k :: Γ) C F ν ∧
    completeInputs k Γ C E F (boxValuation k Γ C E F word) =
      completeInputs k Γ C E F ν ∧
    smallBranch k Γ C E F (boxValuation k Γ C E F word)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Targets
