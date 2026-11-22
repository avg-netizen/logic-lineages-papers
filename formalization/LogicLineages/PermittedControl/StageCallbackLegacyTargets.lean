module
public import LogicLineages.PermittedControl.StageCallbackSupplierTargets
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackLegacy
open OrdinalComparison
open StageCallbackSupplier (Supplier SupplierShape SupplierExact packets compile stageChildren Emits)
open ActualPaidMixedMatrixTuples (alternatives)
open OriginalPrintedLiteralRowBridge (compileRow)
open OriginalRankedLiteralClauseHigh (highPackets)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawDriver (HighProgram)
open OriginalPrintedRawStageQuery (HighAtStage)

/-- The existing typed route alternatives, read as a per-row supplier.
This is the old noncomputable list in its old order; it is used here only
to show that the supplier interface is inhabited and loses nothing. -/
noncomputable def legacy : Supplier := fun r top row => alternatives r top (compileRow row)

def ExactLegacySupplierShape : Prop := SupplierShape legacy

def ExactLegacySupplierExact : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B → SupplierExact f B legacy

/-- Literal equality of ordered lists with the accepted typed compiler. -/
def ExactLegacyLiteralCompile : Prop :=
  (∀ (r top : Nat) (family : Family), packets legacy r top family = highPackets r top family) ∧
  ∀ (C : Nat) (family : Family) (names : List Nat),
    compile legacy C family names = ActualNamedBitFamilyHighAbove.compile C family names

/-- The stage contract for the accepted typed compiler itself. The raw
emission equation stays a hypothesis: no computable program is exhibited. -/
def ExactLegacyStageCallback : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ high : HighProgram, Emits legacy B high → HighAtStage f B high (stageChildren legacy B)

def FullStageCallbackLegacy : Prop :=
  ExactLegacySupplierShape ∧ ExactLegacySupplierExact ∧ ExactLegacyLiteralCompile ∧
    ExactLegacyStageCallback

end LogicLineages.PermittedControl.StageCallbackLegacy
