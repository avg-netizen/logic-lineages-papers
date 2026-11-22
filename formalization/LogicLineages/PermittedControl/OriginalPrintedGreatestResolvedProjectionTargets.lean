module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosureTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedGreatestGateResolution (resolutionMinimum)
open OriginalPrintedGreatestResolvedMatrix (prefixRows fullRows PacketAccepts)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top replay conjoin atomMap lowerBound)
open OriginalMatrixLinearLowerTable (lowerTable Live assignment)
open OriginalMatrixDenseRanks (support renameRow)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open OriginalProjectedMatrixSemantics (MatrixAccepts availabilityRows)
open OriginalProjectedMatrixDecode (decode)
open ActualFiniteOrderBranches (Pattern rename guard realized)
open HeterogeneousSignedMatrixSlice (Row)
open SignedRowGuardedTest (Test)
open OriginalMatrixLinearRowFormula (rowFormula choosePolarity)

noncomputable def ranked (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) : List Row :=
  (fullRows known gates p branch).map (renameRow (rename branch))

noncomputable def table (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) : List LowerOperand :=
  lowerTable (top branch) (ranked known gates p branch)

/-- Total syntactic decisor for the original signed row admission. An
inadmissible modulus cannot be promoted to a successful graph row. -/
def admittedCode : Test → Bool
  | .congruence m => decide (0 < m)
  | _ => true

noncomputable def emit (branch : Pattern) (ops : List LowerOperand) (r : Row) : NormalForm.Formula :=
  if admittedCode r.1 then rowFormula (top branch) ops (renameRow (rename branch) r) else .falsity

noncomputable def formula (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (minimum : Nat) (positive : Bool) : NormalForm.Formula :=
  let compile := emit branch (table known gates p branch)
  .conjunction (lowerBound minimum)
    (.conjunction (conjoin ((prefixRows known gates p branch).map compile))
      (choosePolarity (atomMap (fun a => compile (OriginalPlainTerminalMatrix.atomRow a)) p) positive))

def ExactResolvedPrepared : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      ∀ (minimum : Nat) (positive : Bool),
        let ops := table known gates p branch
        let q := formula known gates p branch minimum positive
        PreparedInput ops q ∧
        ∀ (ν : Nat → Nat), PreparedTableTied f (top branch) (realized θ branch) ops ν →
          ∀ z : Nat, q.eval (Function.update ν 0 z) ↔
            minimum ≤ z ∧ PacketAccepts f (replay θ known gates p branch z)
              (prefixRows known gates p branch) p positive

def ExactResolvedProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
        (∀ z : Nat, prior (replay θ known gates p branch z) ↔ prior θ) →
        let ops := table known gates p branch
        let minimum := resolutionMinimum B θ known gates p branch
        let q := formula known gates p branch minimum positive
        ((prior θ ∧ Live f (realized θ branch) ops ∧
          (eliminatePreparedFormula q).eval (assignment f (realized θ branch) ops)) ↔
          ∃ z : Nat, minimum ≤ z ∧ prior (replay θ known gates p branch z) ∧
            SourceAccepts f (replay θ known gates p branch z) known gates p positive)

def ExactResolvedProjectionDecrease : Prop :=
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      let ops := table known gates p branch
      let original := renamed known gates p branch
      argumentNames ops ⊆ (supportSet original).erase (top branch) ∧
        (argumentNames ops).card < dimension original

def ExactResolvedResidualClosure : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
        (∀ z : Nat, prior (replay θ known gates p branch z) ↔ prior θ) →
        let ops := table known gates p branch
        let bound := resolutionMinimum B θ known gates p branch
        let out := eliminatePreparedFormula (formula known gates p branch bound positive)
        ∃ rows : List Row, decode ops out = some rows ∧
          supportSet (availabilityRows ops ++ rows) = argumentNames ops ∧
          dimension (availabilityRows ops ++ rows) < dimension (renamed known gates p branch) ∧
          ((prior θ ∧ MatrixAccepts f (realized θ branch) ops out true rows) ↔
            ∃ z : Nat, bound ≤ z ∧ prior (replay θ known gates p branch z) ∧
              SourceAccepts f (replay θ known gates p branch z) known gates p positive)

def FullOriginalPrintedGreatestResolvedProjection : Prop :=
  ExactResolvedPrepared ∧ ExactResolvedProjection ∧ ExactResolvedProjectionDecrease ∧
    ExactResolvedResidualClosure

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
