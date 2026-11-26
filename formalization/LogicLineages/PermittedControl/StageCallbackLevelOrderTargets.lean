module
public import LogicLineages.PermittedControl.StageCallbackCanonicalSupplierTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackLevelOrder
open OrdinalComparison
open StageCallbackSupplier (Supplier SupplierShape SupplierExact stageChildren Emits)
open StageCallbackCanonicalRoutes (CanonicalActive tapes guard routes)
open StageCallbackCanonicalSupplier (canonical)
open ActualCanonicalOperandGrouping (groupTyped)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (Route)
open ActualSelectedSignedRoutePacket (packet)
open ActualPaidMixedMatrixTuples (MixedRow)
open ActualSyntaxChargeBudget (syntaxBudget)
open OriginalPrintedLiteralRowBridge (compileRow)
open ActualBitFamilyRawDriver (HighProgram)
open OriginalPrintedRawStageQuery (HighAtStage)

/-- One frontier entry: the guards met so far, in path order, and the
current syntax. This is the typed shadow of what a raw level iteration
carries (a list of packet codes and a raw syntax). -/
abbrev Entry := List Packet × SyntaxState

/-- The zero-edge child of an entry along one tape, if any. -/
noncomputable def stepOf (top : Nat) (e : Entry) (a : List Answer) : Option Entry :=
  if maximalCoefficient (groupTyped e.2.terms) a = 0 then
    (canonicalSuccessor e.2.constant e.2.terms a).map
      (fun out => (e.1 ++ [guard top (groupTyped e.2.terms) a],out))
  else none

open scoped Classical in
/-- Children exist only at a node active at the greatest rank. This is
the activity test the accepted raw step does not make. -/
noncomputable def children (top : Nat) (e : Entry) : List Entry :=
  if CanonicalActive top e.2.terms then
    (tapes (groupTyped e.2.terms)).filterMap (stepOf top e)
  else []

/-- The signed leaf of an entry along one nonzero tape, if any. -/
noncomputable def leafOf (top : Nat) (e : Entry) (a : List Answer) : Option Route :=
  if maximalCoefficient (groupTyped e.2.terms) a = 0 then none
  else some ⟨e.1 ++ [guard top (groupTyped e.2.terms) a],
    .signed (maximalCoefficient (groupTyped e.2.terms) a)⟩

open scoped Classical in
/-- Only stopped candidates: the linear exit of an inactive entry, or one
signed leaf per nonzero tape of an active entry. -/
noncomputable def leaves (top : Nat) (test : OrderTest) (positive : Bool) (e : Entry) :
    List Route :=
  if CanonicalActive top e.2.terms then
    (tapes (groupTyped e.2.terms)).filterMap (leafOf top e)
  else [⟨e.1,.linear (canonicalPacket top e.2.constant e.2.terms test.test positive)⟩]

/-- Plain iteration of the level step on a list, as a raw program runs it. -/
noncomputable def level (top : Nat) (start : SyntaxState) : Nat → List Entry
  | 0 => [([],start)]
  | n+1 => (level top start n).flatMap (children top)

/-- Leaves of levels `0,…,fuel`, level by level. -/
noncomputable def levelRoutes (top : Nat) (test : OrderTest) (positive : Bool) (fuel : Nat)
    (s : SyntaxState) : List Route :=
  (List.range (fuel+1)).flatMap
    (fun n => (level top s n).flatMap (leaves top test positive))

noncomputable def alternatives (r top : Nat) : MixedRow → List Packet
  | .signed row =>
      (levelRoutes top row.test row.positive (syntaxBudget r row.source.terms) row.source).map
        (packet row.test row.positive)
  | .modular m s positive => [ActualGreatestCongruenceRoute.packet top m s positive]

/-- The supplier in the list order of a raw level iteration. Still typed
and `noncomputable`. -/
noncomputable def levelOrder : Supplier := fun r top row => alternatives r top (compileRow row)

/-- Same routes as the depth-first tree, as sets. No claim about order
or multiplicity. -/
def ExactLevelOrderRoutes : Prop :=
  ∀ (top : Nat) (test : OrderTest) (positive : Bool) (fuel : Nat) (s : SyntaxState)
    (route : Route),
    route ∈ levelRoutes top test positive fuel s ↔ route ∈ routes top test positive fuel s

def ExactLevelOrderMembers : Prop :=
  ∀ (r top : Nat) (row : OriginalPrintedTerminalBitClauses.BitRow) (q : Packet),
    q ∈ levelOrder r top row ↔ q ∈ canonical r top row

/-- The supplier interface uses membership only. -/
def ExactSupplierMemberTransfer : Prop :=
  ∀ (alt alt' : Supplier),
    (∀ (r top : Nat) (row : OriginalPrintedTerminalBitClauses.BitRow) (q : Packet),
      q ∈ alt' r top row ↔ q ∈ alt r top row) →
    (SupplierShape alt → SupplierShape alt') ∧
    ∀ (f : Nat → Nat) (B : Nat), SupplierExact f B alt → SupplierExact f B alt'

def ExactLevelOrderSupplierShape : Prop := SupplierShape levelOrder

def ExactLevelOrderSupplierExact : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B → SupplierExact f B levelOrder

/-- The stage contract restated for the one supplier the close step will
use. The emission equation is still a hypothesis. -/
def ExactLevelOrderStageCallback : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ high : HighProgram, Emits levelOrder B high →
      HighAtStage f B high (stageChildren levelOrder B)

def FullStageCallbackLevelOrder : Prop :=
  ExactLevelOrderRoutes ∧ ExactLevelOrderMembers ∧ ExactSupplierMemberTransfer ∧
    ExactLevelOrderSupplierShape ∧ ExactLevelOrderSupplierExact ∧ ExactLevelOrderStageCallback

end LogicLineages.PermittedControl.StageCallbackLevelOrder
