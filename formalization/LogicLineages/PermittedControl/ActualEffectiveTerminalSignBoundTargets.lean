module
public import LogicLineages.PermittedControl.ActualTraceSignCutoffTargets
public import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetCodeTargets
public import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open ActualMixedRowLeadingSum ActualReadChargeIteration ActualFiniteGlobalTail
open ActualZeroClassCommonTail ActualTraceSignCutoff ActualZeroEdgeConstantShift
open ActualZeroEdgeAlphabet ActualZeroEdgeAlphabetCode ActualSyntaxChargeBudget

def correctionMaxCode (alphabet : AlphabetCode) : Nat :=
  finiteMax correctionBoundCode alphabet

def shortLengthCode (op : LowerOperandCode) : Nat :=
  if op.1 = 2 then shortGapLengthCode op.2.2.2.2.1 op.2.2.2.2.2 else 0

def prefixShortMaxCode (alphabet : AlphabetCode) : Nat :=
  finiteMax (fun p : PrefixCode => shortGapLengthCode p.2.1 p.2.2) (prefixChoicesCode alphabet)

def cleanupMaxCode (alphabet : AlphabetCode) : Nat :=
  finiteMax shortLengthCode (expandCode alphabet)

def edgeFactorCode (alphabet : AlphabetCode) : Nat :=
  correctionMaxCode alphabet + prefixShortMaxCode alphabet + 3 * cleanupMaxCode alphabet

def syntaxMass (terms : List WeightedOperand) : Nat :=
  terms.foldr (fun t rest => t.1.natAbs + rest) 0

def syntaxMassCode (terms : List WeightedCode) : Nat :=
  terms.foldr (fun t rest => t.1.natAbs + rest) 0

noncomputable def depthAlphabet (budget : Nat) (terms : List WeightedOperand) : List LowerOperand :=
  (List.range (budget+1)).flatMap (fun depth => expandSteps depth (terms.map Prod.snd))

noncomputable def signCeilingAtBudget (budget : Nat) (c : Int) (terms : List WeightedOperand) : Nat :=
  let alphabet := depthAlphabet budget terms
  let mass := 3 ^ budget * syntaxMass terms
  let constant := c.natAbs + budget * (mass * edgeFactor alphabet)
  SelectedLeadingSignCutoff.cutoff (2 * mass) (constant + mass * correctionMaximum alphabet)

/-- Supplied-depth raw calculation. One extra expansion in edgeFactorCode
covers cleaned-away short keys. The initial signed constant is retained. -/
def signCeilingAtBudgetCode (budget : Nat) (c : Int) (terms : List WeightedCode) : Nat :=
  let alphabet := collectCode budget (terms.map Prod.snd)
  let mass := 3 ^ budget * syntaxMassCode terms
  let constant := c.natAbs + budget * (mass * edgeFactorCode alphabet)
  SelectedLeadingSignCutoff.cutoff (2 * mass) (constant + mass * correctionMaxCode alphabet)

def inputSignBoundCode (r : Nat) (c : Int) (terms : List WeightedCode) : Nat :=
  signCeilingAtBudgetCode (syntaxBudgetCode r terms) c terms

def CodeEffectivity : Prop :=
  Primrec (fun p : Nat × Int × List WeightedCode => signCeilingAtBudgetCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Int × List WeightedCode => inputSignBoundCode p.1 p.2.1 p.2.2)

def CodeCalibration : Prop :=
  (∀ (budget : Nat) (c : Int) (terms : List WeightedOperand),
    signCeilingAtBudgetCode budget c (terms.map encodeWeighted) = signCeilingAtBudget budget c terms) ∧
  ∀ (r : Nat) (c : Int) (terms : List WeightedOperand),
    inputSignBoundCode r c (terms.map encodeWeighted) = signCeilingAtBudget (syntaxBudget r terms) c terms

/-- Inequality, not equality with the exact-charge #949 uniform cutoff. -/
def ExactSignBoundDominance : Prop :=
  ∀ (r : Nat) (initial : ReadState),
    terminalCutoffCeiling r initial ≤
      inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted)

def FullActualEffectiveTerminalSignBound : Prop :=
  CodeEffectivity ∧ CodeCalibration ∧ ExactSignBoundDominance

end LogicLineages.PermittedControl.ActualEffectiveTerminalSignBound
