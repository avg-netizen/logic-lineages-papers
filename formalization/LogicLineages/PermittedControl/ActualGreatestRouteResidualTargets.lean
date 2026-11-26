module
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets
public import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupportTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestRouteResidual
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open OriginalProjectedMatrixDecode (decode)
open OriginalProjectedMatrixSemantics (MatrixAccepts availabilityRows)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open HeterogeneousSignedMatrixSlice (Row)
open OriginalMatrixLowDimension (supportSet dimension)

def StrictLower (top : Nat) (ops : List LowerOperand) : Prop :=
  ∀ op ∈ ops, op.rank < top

def keep (top : Nat) (qs : List Packet) : List Packet :=
  qs.filter (fun q => q.1.all (fun op => decide (op.rank < top)))

structure Residual where
  ops : List LowerOperand
  formula : NormalForm.Formula
  atoms : List Row

noncomputable def decodeRoute (minimum : Nat) (q : Packet) : Option Residual :=
  let output := project minimum q
  (decode output.1 output.2).map (fun rs => ⟨output.1,output.2,rs⟩)

noncomputable def lowerFamily (top minimum : Nat) (qs : List Packet) : List Residual :=
  (keep top qs).filterMap (decodeRoute minimum)

def rows (p : Residual) : List Row := availabilityRows p.ops ++ p.atoms

def LowerMatrix (f ρ : Nat → Nat) (p : Residual) : Prop :=
  MatrixAccepts f ρ p.ops p.formula true p.atoms

def ExactKeptActualRoute : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (qs : List Packet),
    ((∃ q ∈ qs, LowerHolds f ρ top q) ↔ ∃ q ∈ keep top qs, LowerHolds f ρ top q)

def ExactDecodedActualResidual : Prop :=
  ∀ (f ρ : Nat → Nat) (top minimum : Nat) (q : Packet), Shape q → StrictLower top q.1 →
    ∃ output : Residual, decodeRoute minimum q = some output ∧
      output.ops = q.1 ∧
      supportSet (rows output) = argumentNames q.1 ∧
      (∀ rank ∈ supportSet (rows output), rank < top) ∧
      (LowerHolds f ρ top (project minimum q) ↔ LowerMatrix f ρ output)

def ExactActualLowerRouteFamily : Prop :=
  ∀ (f ρ : Nat → Nat) (top minimum : Nat) (qs : List Packet),
    (∀ q ∈ qs, Shape q) →
      (∀ p ∈ lowerFamily top minimum qs, ∀ rank ∈ supportSet (rows p), rank < top) ∧
      ((∃ q ∈ qs, LowerHolds f ρ top (project minimum q)) ↔
        ∃ p ∈ lowerFamily top minimum qs, LowerMatrix f ρ p)

def ExactActualLowerRouteDimension : Prop :=
  ∀ (top minimum : Nat) (qs : List Packet) (source : List Row),
    (∀ q ∈ qs, Shape q) → (∀ rank ≤ top, rank ∈ supportSet source) →
    ∀ p ∈ lowerFamily top minimum qs,
      supportSet (rows p) ⊆ (supportSet source).erase top ∧ dimension (rows p) < dimension source

def FullActualGreatestRouteResidual : Prop :=
  ExactKeptActualRoute ∧ ExactDecodedActualResidual ∧ ExactActualLowerRouteFamily ∧ ExactActualLowerRouteDimension

end LogicLineages.PermittedControl.ActualGreatestRouteResidual
