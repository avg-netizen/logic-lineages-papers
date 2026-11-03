module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntaxDefinitions
public import LogicLineages.OrdinalComparison.SingleCorePresburgerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox
open BalancedSyntax

/-- The literal original pair support, before any collection, cancellation or
guard simplification. Zero outside multiples were already excluded by the
source syntax. The one shared certificate is retained throughout. -/
def sourceAmbient (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) : List Nat :=
  rawVariables (k :: Γ) C E ++ rawVariables (k :: Γ) C F

/-- Only repeated RAW NAMES are removed for box coordinates. Repeated or
dependent basis expressions remain in the original ordered certificate. -/
def sourceSupport (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) : List Nat :=
  (sourceAmbient k Γ C E F).dedup

/-- All raw names in the whole common basis, including entries needed only
by an outside remainder. Any original atom exposes this entire support. -/
def basisSupport (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ)) : List Nat :=
  (List.finRange k).flatMap (fun j => rawVariables Γ C.1 (C.2 j))

def positiveOn (support : List Nat) (ν : Nat → Nat) : Prop :=
  ∀ i ∈ support, 0 < ν i

/-- EVERY original complete norm input in signed-row occurrence order. An
occurrence is retained even when its eventual collected block cancels. -/
noncomputable def completeInputs (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (ν : Nat → Nat) : List Nat :=
  (comparisonRow E F).atoms.map (fun a => BalancedRow.input (basisValues k Γ C ν) a.2)

/-- The threshold of the ORIGINAL signed row, not a survivor threshold or
an enlarged bound. This is exactly the paper's balanced L. -/
noncomputable def originalThreshold {k : Nat} (E F : Upper k) : Nat :=
  BalancedRow.threshold (comparisonRow E F)

/-- One original complete input below the original L triggers the small
branch. In particular this branch is false when there are no atoms. -/
def smallBranch (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (ν : Nat → Nat) : Prop :=
  ∃ a ∈ (comparisonRow E F).atoms,
    BalancedRow.input (basisValues k Γ C ν) a.2 < originalThreshold E F

/-- Reuse the existing finite words literally: [1,L-1] on the deduplicated
actual raw support, with one empty word when that support is empty. -/
noncomputable def boxWords (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) : List (List Nat) :=
  singleCoreBoxWords (originalThreshold E F) (sourceSupport k Γ C E F).length

/-- Valid box words give positive representatives defaulting to ONE outside
actual support. That default is for evaluating representatives, not a
restriction on the original raw valuation, whose outside coordinates remain
arbitrary. -/
def boxValuation (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (word : List Nat) : Nat → Nat :=
  singleCoreBoxLookup (sourceSupport k Γ C E F) word

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox
