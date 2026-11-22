module
public import LogicLineages.PermittedControl.OriginalGreatestGateGrowthTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolution
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (circuit)
open OriginalPrintedPlainMatrixOrderBranches (branches SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top replay safeMinimum)
open ActualFiniteOrderBranches (Pattern rename guard)
open OriginalGreatestGateGrowth (longCountBound)
open OriginalMixedTerminalTest (Test)

inductive Mode where
  | keep (g : NormalizedGate)
  | impossible
  | shortCount (lam mu : NONote) (source output : Nat)

/-- Literal normalized gate classification on one ordered rank pattern,
before its actual greatest numerical value is known. -/
def mode (label : Nat → Nat) (greatest : Nat) (g : NormalizedGate) : Mode :=
  match g with
  | .base (.limitPair _ _ s _) => if label s = greatest then .impossible else .keep g
  | .field (.iterate (k+1) s _) => if label s = greatest then .impossible else .keep g
  | .field (.entry (.proper _ _) s _) => if label s = greatest then .impossible else .keep g
  | .field (.count (.proper lam mu) s o) =>
      if label s = greatest then
        if 0 < shortGapLength lam mu then .shortCount lam mu s o else .impossible
      else .keep g
  | _ => .keep g

def Mode.Holds (f θ : Nat → Nat) : Mode → Prop
  | .keep g => g.graph f θ
  | .impossible => False
  | .shortCount lam mu s o =>
      ProperField (.entry 0 lam mu) ∧ actualOrdinalNorm lam.1.repr ≤ θ s ∧
        θ o = shortGapLength lam mu

def gateBound : NormalizedGate → Nat
  | .field (.count (.proper lam mu) _ _) =>
      if shortGapLength lam mu = 0 then longCountBound lam mu else 0
  | _ => 0

def familyBound (gs : List NormalizedGate) : Nat :=
  gs.foldr (fun g n => max (gateBound g) n) 0

noncomputable def resolutionMinimum (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) : Nat :=
  max (safeMinimum B θ known gates p branch) (familyBound (circuit known gates p))

noncomputable def plan (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) : List Mode :=
  (circuit known gates p).map (mode (rename branch) (top branch))

def ExactUniformGateResolution : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      ∀ z : Nat, resolutionMinimum B θ known gates p branch ≤ z →
        ∀ g ∈ circuit known gates p,
          let ν := replay θ known gates p branch z
          (g.graph f ν ↔ (mode (rename branch) (top branch) g).Holds f ν)

def ExactUniformOriginalResolvedBranch : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      ∀ z : Nat, resolutionMinimum B θ known gates p branch ≤ z →
        ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
          let ν := replay θ known gates p branch z
          ((prior ν ∧ SourceAccepts f ν known gates p positive) ↔
            prior ν ∧ (∀ step ∈ plan known gates p branch, step.Holds f ν) ∧
              (Test.rows p).atPolarity positive ν)

def FullOriginalPrintedGreatestGateResolution : Prop :=
  ExactUniformGateResolution ∧ ExactUniformOriginalResolvedBranch

end LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolution
