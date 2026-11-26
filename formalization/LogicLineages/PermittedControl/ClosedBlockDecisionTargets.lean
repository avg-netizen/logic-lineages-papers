module
public import LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQueryTargets
public import LogicLineages.PermittedControl.StageCallbackSupplierTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ClosedBlockDecision
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate Topological)
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedRawFamilyFrontend (Args encodeInput)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open OriginalPrintedRawConditionalQuery (EverySuccessfulObservation)
open OriginalPrintedRawSelectedStageQuery (ForControl)
open ActualBitFamilyRawDriver (HighProgram)
open StageCallbackSupplier (Supplier SupplierShape SupplierExact Emits)

/-- `decide` answers the printed closed-block queries for the control `f`:
on every encoded topological circuit and plain prepared matrix, the
existential query, its negation, and the universal query through the
opposite polarity. Literally the three clauses of `ForControl`. -/
def Decides (f : Nat → Nat) (decide : Args → Option Bool) : Prop :=
  ∀ (known : List Nat) (gs : List Gate) (p : NormalForm.Formula),
    Topological known gs → PlainPreparedFormula p → ∀ positive : Bool,
      (decide (encodeInput known gs p positive) = some true ↔
        HasSuccessfulObservation f gs p positive) ∧
      (decide (encodeInput known gs p positive) = some false ↔
        ¬ HasSuccessfulObservation f gs p positive) ∧
      (decide (encodeInput known gs p (!positive)) = some false ↔
        EverySuccessfulObservation f gs p positive)

/-- Closed existential and closed universal blocks are decidable for `f`:
one computable procedure, with no callback left as a parameter. -/
def DecidableClosedBlocks (f : Nat → Nat) : Prop :=
  ∃ decide : Args → Option Bool, Computable decide ∧ Decides f decide

/-- Comparator for Paper 17 `thm:arithmetic` (closed-block decision) at
the two controls of the paper, in the vocabulary of the accepted stage
query #1372. Not proved here. -/
def ClosedBlockDecision : Prop :=
  DecidableClosedBlocks factorialControl ∧ ∀ b : Nat, DecidableClosedBlocks (nearControl b)

/-- The single obligation that remains for a control with threshold `B`:
some shaped exact per-row supplier whose encoded stage children are emitted
by a computable raw program. Purely an emission statement plus the
supplier interface of #1387; no semantic clause about the callback. -/
def ComputableEmitter (f : Nat → Nat) (B : Nat) : Prop :=
  ∃ alt : Supplier, SupplierShape alt ∧ SupplierExact f B alt ∧
    ∃ high : HighProgram, Computable high ∧ Emits alt B high

def ExactClosedBlockFromEmitter : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), ForControl f B → ComputableEmitter f B → DecidableClosedBlocks f

/-- `thm:arithmetic`'s comparator follows from a computable emitter at the
factorial control with threshold 0 and at every near control with its
threshold `b + 1`. -/
def ExactClosedBlockReduction : Prop :=
  ComputableEmitter factorialControl 0 → (∀ b : Nat, ComputableEmitter (nearControl b) (b + 1)) →
    ClosedBlockDecision

def FullClosedBlockDecisionReduction : Prop :=
  ExactClosedBlockFromEmitter ∧ ExactClosedBlockReduction

end LogicLineages.PermittedControl.ClosedBlockDecision
