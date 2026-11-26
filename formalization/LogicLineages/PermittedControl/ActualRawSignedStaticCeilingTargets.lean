module
public import LogicLineages.PermittedControl.ActualRawComparisonCeilingTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingTargets
public import LogicLineages.PermittedControl.ActualEffectiveGlobalTailTargets
public import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundTargets
public import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawSignedStaticCeiling
open MixedSameRankResidue (WeightedCode encodeWeighted)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualPaidSignedRouteReplay (commonMinimum dummy)
open ActualTraceSignCutoff (terminalCutoffCeiling)
open ActualEffectiveGlobalTail (inputTailCode)
open ActualEffectiveTerminalSignBound (inputSignBoundCode)
open ActualRawComparisonCeiling (cutoffCode)
open ActualBitFamilyRawReadCeiling (termsCode)

abbrev RawSyntax := Int × List WeightedCode

def encodeSyntax (s : SyntaxState) : RawSyntax :=
  (s.constant,s.terms.map encodeWeighted)

def commonCode (B r : Nat) (s : RawSyntax) : Nat :=
  max (termsCode s.2) (max (inputTailCode B r s.2) (cutoffCode B r s.2))

def signCode (r : Nat) (s : RawSyntax) : Nat := inputSignBoundCode r s.1 s.2

def staticCode (B r : Nat) (s : RawSyntax) : Nat := max (commonCode B r s) (signCode r s)

def ExactCommonMinimumMajorant : Prop :=
  ∀ (B r : Nat) (s : SyntaxState), commonMinimum B r s ≤ commonCode B r (encodeSyntax s)

def ExactTerminalCutoffMajorant : Prop :=
  ∀ (r : Nat) (s : SyntaxState), terminalCutoffCeiling r (dummy s) ≤ signCode r (encodeSyntax s)

def ExactRawSignedStaticMajorant : Prop :=
  ∀ (B r : Nat) (s : SyntaxState),
    max (commonMinimum B r s) (terminalCutoffCeiling r (dummy s)) ≤ staticCode B r (encodeSyntax s)

def ExactRawSignedStaticEffectivity : Prop :=
  Primrec (fun p : Nat × Nat × RawSyntax => commonCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × RawSyntax => signCode p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × RawSyntax => staticCode p.1 p.2.1 p.2.2)

def FullActualRawSignedStaticCeiling : Prop :=
  ExactCommonMinimumMajorant ∧ ExactTerminalCutoffMajorant ∧
    ExactRawSignedStaticMajorant ∧ ExactRawSignedStaticEffectivity

end LogicLineages.PermittedControl.ActualRawSignedStaticCeiling
