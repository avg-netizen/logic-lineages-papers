module
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReads
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand properOperand orderedReads actualSum)
open ActualReadChargeIteration (ReadState)
open ActualZeroClassReplacement (liftedReads)
open ActualFiniteGlobalTail (syntaxOf)
open ActualBoundedSignedRouteSemantics (stateSyntax)
open ActualSymbolicZeroSuccessor (SyntaxState)

noncomputable def intervalMinimum (lam mu : NONote) : Nat :=
  max 2 (max (actualOrdinalNorm lam.1.repr) (actualOrdinalNorm mu.1.repr))

noncomputable def operandMinimum : LowerOperand → Nat
  | .coordinate _ | .ordinary _ (.iterate _) => 0
  | .ordinary _ (.entry _ lam mu) | .count _ lam mu => intervalMinimum lam mu

noncomputable def readCeiling (ts : List WeightedOperand) : Nat :=
  ts.foldr (fun t n => max (operandMinimum t.2) n) 0

def PaidReadCeiling (ρ : Nat → Nat) (ts : List WeightedOperand) : Prop :=
  ∀ t ∈ ts, readCeiling ts ≤ ρ t.2.rank

def ExactPaidOperandRead : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (op : LowerOperand), properOperand op → operandMinimum op ≤ ρ op.rank →
      ∃ v : Nat, LowerOperandActual f ρ op v ∧ lowerOperandRead f ρ op = some (some v)

def ExactPaidOrderedSyntaxReads : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (ρ : Nat → Nat) (s : SyntaxState),
      (∀ t ∈ s.terms, properOperand t.2) → PaidReadCeiling ρ s.terms →
      ∃ original : ReadState, stateSyntax original = s ∧ liftedReads f ρ original.reads

def FullActualPaidOrderedSyntaxReads : Prop :=
  ExactPaidOperandRead ∧ ExactPaidOrderedSyntaxReads

end LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReads
