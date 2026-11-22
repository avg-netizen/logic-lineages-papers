module
public import LogicLineages.PermittedControl.StageCallbackSupplierTargets
public import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackCanonicalSupplier
open OrdinalComparison
open StageCallbackSupplier (Supplier SupplierShape SupplierExact stageChildren Emits)
open StageCallbackCanonicalRoutes (routes)
open ActualPreparedSlotAppend (Packet)
open ActualPaidMixedMatrixTuples (MixedRow)
open ActualSelectedSignedRoutePacket (packet)
open ActualSyntaxChargeBudget (syntaxBudget)
open OriginalPrintedLiteralRowBridge (compileRow)
open ActualBitFamilyRawDriver (HighProgram)
open OriginalPrintedRawStageQuery (HighAtStage)

/-- Alternatives of one compiled row. A signed row gets the rendered
canonical routes of its cleaned syntax at the syntax budget; a congruence
row keeps its one accepted literal-order packet. -/
noncomputable def alternatives (r top : Nat) : MixedRow → List Packet
  | .signed row =>
      (routes top row.test row.positive (syntaxBudget r row.source.terms) row.source).map
        (packet row.test row.positive)
  | .modular m s positive => [ActualGreatestCongruenceRoute.packet top m s positive]

/-- The canonical per-row supplier on literal bit rows. Typed and
`noncomputable`; its list order is the depth-first order of the route tree. -/
noncomputable def canonical : Supplier := fun r top row => alternatives r top (compileRow row)

def ExactCanonicalSupplierShape : Prop := SupplierShape canonical

/-- The canonical supplier meets the frozen turn-001 interface as it
stands: the raw row majorant offered there pays every canonical need. -/
def ExactCanonicalSupplierExact : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B → SupplierExact f B canonical

/-- Hence the stage contract for the canonical children. The emission
equation remains a hypothesis: no raw program is exhibited. -/
def ExactCanonicalStageCallback : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ high : HighProgram, Emits canonical B high → HighAtStage f B high (stageChildren canonical B)

def FullStageCallbackCanonicalSupplier : Prop :=
  ExactCanonicalSupplierShape ∧ ExactCanonicalSupplierExact ∧ ExactCanonicalStageCallback

end LogicLineages.PermittedControl.StageCallbackCanonicalSupplier
