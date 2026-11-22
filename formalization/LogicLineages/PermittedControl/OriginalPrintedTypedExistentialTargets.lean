module
public import LogicLineages.PermittedControl.ActualBitFamilyTypedFuelTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesTargets
public import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedExistential
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (PlainPreparedFormula)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyExistentialLow (Satisfiable)
open ActualBitFamilyTypedFuel (solve)
open OriginalPrintedCircuitSequential (Gate Topological)
open OriginalPrintedCircuitTerminal (observe)
open OriginalPrintedPlainMatrixInfiniteLow (circuit)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalPrintedTerminalBitClauses (clauses)

noncomputable def literalFamily (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) : Family :=
  clauses (OriginalNormalizedCircuitMatrix.rowsList (circuit known gates p))
    (OriginalPlainTerminalMatrix.rows p) p positive

/-- A logical noncomputable result on the actual plain typed original
finite circuit; no raw quantifier compiler or execution claim. -/
noncomputable def solveOriginal (f : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) : Bool :=
  solve f B (literalFamily known gates p positive)

def HasSuccessfulObservation (f : Nat → Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) : Prop :=
  ∃ base : Nat → Nat, observe f base gates (.rows p) = .ok positive

def ExactOriginalLiteralFamilyExistential : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p → ∀ positive : Bool,
      (Satisfiable f (literalFamily known gates p positive) ↔
        ∃ θ : Nat → Nat, SourceAccepts f θ known gates p positive)

def ExactOriginalTypedObservationExistential : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    Topological known gates → PlainPreparedFormula p → ∀ positive : Bool,
      ((∃ θ : Nat → Nat, SourceAccepts f θ known gates p positive) ↔
        HasSuccessfulObservation f gates p positive)

def ExactOriginalPrintedTypedExistential : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      Topological known gates → PlainPreparedFormula p → ∀ positive : Bool,
        (solveOriginal f B known gates p positive = true ↔ HasSuccessfulObservation f gates p positive) ∧
        (solveOriginal f B known gates p positive = false ↔ ¬ HasSuccessfulObservation f gates p positive)

def FullOriginalPrintedTypedExistential : Prop :=
  ExactOriginalLiteralFamilyExistential ∧ ExactOriginalTypedObservationExistential ∧
    ExactOriginalPrintedTypedExistential

end LogicLineages.PermittedControl.OriginalPrintedTypedExistential
