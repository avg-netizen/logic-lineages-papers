module
public import LogicLineages.PermittedControl.OriginalPrintedNewCutoffLowTargets
public import LogicLineages.PermittedControl.OriginalPrintedHighResidualTargets
public import LogicLineages.PermittedControl.OriginalPrintedZeroSupportTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedDimensionRound
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts renamed)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedRankedLiteralHigh (cutoff chartMinimum PaidSupport)
open OriginalPrintedHighResidual (GuardedAccepts guardedRows outcomes)
open OriginalMatrixDenseRanks (support)
open OriginalMatrixLowDimension (supportSet dimension)
open ActualFiniteOrderBranches (Pattern guard realized)
open HeterogeneousSignedMatrixLowStrips (Branch)
open HeterogeneousSignedMatrixSlice (Row HitRows)
open ActualGreatestRouteResidual (Residual)

inductive Query where
  | closed (θ : Nat → Nat)
  | low (baseline : Nat → Nat) (name : Nat)
  | high (baseline : Nat → Nat) (chart : Pattern)

inductive Plan where
  | closed (θ : Nat → Nat) (answer : Option Bool)
  | low (baseline : Nat → Nat) (name : Nat) (children : List Branch)
  | high (baseline : Nat → Nat) (chart : Pattern) (children : List Residual)

def Ready (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (prior : (Nat → Nat) → Prop) : Query → Prop
  | .closed θ => support (matrix known gates p) = []
  | .low _ name => name ∈ support (matrix known gates p)
  | .high θ chart =>
      PaidSupport B θ known gates p positive ∧
      chart ∈ OriginalPrintedPlainMatrixOrderBranches.branches known gates p ∧
      (guard chart).eval θ ∧ 0 < chart.1 ∧
      ∀ z : Nat, chartMinimum B θ known gates p positive chart ≤ z →
        (prior (replay θ known gates p chart z) ↔ prior θ)

/-- A high query is genuinely existential over greatest replay. It is
not pointwise truth at the baseline. A low query varies only one name. -/
def Source (f : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (prior : (Nat → Nat) → Prop) : Query → Prop
  | .closed θ => prior θ ∧ SourceAccepts f θ known gates p positive
  | .low ρ name =>
      ∃ a : Nat, a < cutoff B known gates p positive ∧ let θ := Function.update ρ name a
      prior θ ∧ SourceAccepts f θ known gates p positive
  | .high θ chart =>
      ∃ z : Nat, chartMinimum B θ known gates p positive chart ≤ z ∧
        prior (replay θ known gates p chart z) ∧
        SourceAccepts f (replay θ known gates p chart z) known gates p positive

noncomputable def compile (f : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) : Query → Plan
  | .closed θ => .closed θ (OriginalPrintedZeroSupport.answer known gates p)
  | .low ρ name => .low ρ name
      (HeterogeneousSignedMatrixLowStrips.branches f name (cutoff B known gates p positive) (matrix known gates p))
  | .high θ chart => .high θ chart (outcomes B θ known gates p positive chart)

def Accepts (f : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (prior : (Nat → Nat) → Prop) : Plan → Prop
  | .closed θ output => prior θ ∧ output = some positive
  | .low ρ name children =>
      ∃ branch ∈ children, ∃ rs : List Row,
        HitRows branch.2 rs ∧ supportSet rs = (supportSet (matrix known gates p)).erase name ∧
        dimension rs < dimension (matrix known gates p) ∧
        let θ := Function.update ρ name branch.1
        prior θ ∧ OriginalPrintedNewCutoffLow.Residual f θ known gates p positive rs
  | .high θ chart children =>
      prior θ ∧ ∃ out ∈ children,
        GuardedAccepts f (realized θ chart) (cutoff B known gates p positive) (top chart) out

def SmallerChildren (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) : Plan → Prop
  | .closed .. => True
  | .low _ name children =>
      ∀ branch ∈ children, ∀ rs : List Row, HitRows branch.2 rs →
        supportSet rs = (supportSet (matrix known gates p)).erase name ∧
        dimension rs < dimension (matrix known gates p)
  | .high _ chart children =>
      ∀ out ∈ children, supportSet (guardedRows (cutoff B known gates p positive) (top chart) out) ⊆
        (supportSet (renamed known gates p chart)).erase (top chart) ∧
        dimension (guardedRows (cutoff B known gates p positive) (top chart) out) <
          dimension (renamed known gates p chart)

/-- A single exact original typed round. No recursive application of
compile to a returned row list is specified or assumed. -/
def ExactOriginalPrintedTypedDimensionRound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (gates : List Gate) (p : NormalForm.Formula), PlainPreparedFormula p →
      ∀ (positive : Bool) (prior : (Nat → Nat) → Prop) (query : Query),
        Ready B known gates p positive prior query →
        let next := compile f B known gates p positive query
        SmallerChildren B known gates p positive next ∧
        (Source f B known gates p positive prior query ↔ Accepts f B known gates p positive prior next)

end LogicLineages.PermittedControl.OriginalPrintedTypedDimensionRound
