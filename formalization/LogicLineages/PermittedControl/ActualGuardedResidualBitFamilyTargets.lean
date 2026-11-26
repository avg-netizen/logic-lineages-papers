module
public import LogicLineages.PermittedControl.OriginalPrintedHighResidualTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGuardedResidualBitFamily
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds clauses)
open ActualGreatestRouteResidual (Residual LowerMatrix)
open OriginalPrintedHighResidual (guardedRows GuardedAccepts)
open ActualLowerRankChartRows (lowerChart)
open OriginalProjectedMatrixSemantics (availabilityRows)

abbrev Family := List (List BitRow)

def reify (C top : Nat) (out : Residual) : Family :=
  (clauses (availabilityRows out.ops) out.atoms out.formula true).map (fun row => lowerChart C top ++ row)

def reifyFamily (C top : Nat) (outs : List Residual) : Family :=
  outs.flatMap (reify C top)

def Holds (f ρ : Nat → Nat) (family : Family) : Prop :=
  ∃ clause ∈ family, ClauseHolds f ρ clause

def ExactGuardedResidualBitFamily : Prop :=
  ∀ (f ρ : Nat → Nat) (C top : Nat) (out : Residual),
    (∀ clause ∈ reify C top out, clause.map Prod.fst = guardedRows C top out) ∧
    (Holds f ρ (reify C top out) ↔ GuardedAccepts f ρ C top out)

def ExactGuardedResidualUnion : Prop :=
  ∀ (f ρ : Nat → Nat) (C top : Nat) (outs : List Residual),
    (∀ clause ∈ reifyFamily C top outs, ∃ out ∈ outs, clause.map Prod.fst = guardedRows C top out) ∧
    (Holds f ρ (reifyFamily C top outs) ↔ ∃ out ∈ outs, GuardedAccepts f ρ C top out)

def FullActualGuardedResidualBitFamily : Prop :=
  ExactGuardedResidualBitFamily ∧ ExactGuardedResidualUnion

end LogicLineages.PermittedControl.ActualGuardedResidualBitFamily
