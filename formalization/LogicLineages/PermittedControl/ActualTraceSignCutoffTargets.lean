module
public import LogicLineages.PermittedControl.ActualZeroEdgeConstantShiftTargets
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualTraceSignCutoff
open MixedSameRankResidue ActualWeightedReadNormalization ActualMixedRowLeadingSum
open ActualReadChargeIteration ActualFiniteGlobalTail ActualSignedReadMass ActualZeroEdgeConstantShift

noncomputable def massCeiling (r : Nat) (initial : ReadState) : Nat :=
  3 ^ syntaxCharge r (syntaxOf initial) * signedMass initial.reads

noncomputable def stepCeiling (r : Nat) (initial : ReadState) : Nat :=
  massCeiling r initial * edgeFactor (globalAlphabet r (syntaxOf initial))

noncomputable def constantCeiling (r : Nat) (initial : ReadState) : Nat :=
  initial.constant.natAbs + syntaxCharge r (syntaxOf initial) * stepCeiling r initial

/-- A uniform numeric majorant for the exact reached #850 signed
cutoff, not a claim that the original greatest coordinate pays it. -/
noncomputable def terminalCutoffCeiling (r : Nat) (initial : ReadState) : Nat :=
  SelectedLeadingSignCutoff.cutoff (2 * massCeiling r initial)
    (constantCeiling r initial + massCeiling r initial *
      correctionMaximum (globalAlphabet r (syntaxOf initial)))

def ExactReachMassCeiling : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank n : Nat) (initial reached : ReadState),
    Trace f B ρ r zRank n initial reached → signedMass reached.reads ≤ massCeiling r initial

def ExactTraceConstantCeiling : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank n : Nat) (initial reached : ReadState),
    Trace f B ρ r zRank n initial reached →
    reached.constant.natAbs ≤ initial.constant.natAbs + n * stepCeiling r initial ∧
    reached.constant.natAbs ≤ constantCeiling r initial

def ExactReachedCutoffDominance : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank n : Nat) (initial reached : ReadState),
    Trace f B ρ r zRank n initial reached →
    ∀ xs, normalizeReads f ρ reached.reads = some xs →
      let terms := xs.map Prod.fst
      SelectedLeadingSignCutoff.cutoff (slopeBound terms)
        (reached.constant.natAbs + offsetBound terms) ≤ terminalCutoffCeiling r initial ∧
      rowCutoffCode reached.constant (terms.map encodeWeighted) ≤ terminalCutoffCeiling r initial

def FullActualTraceSignCutoff : Prop :=
  ExactReachMassCeiling ∧ ExactTraceConstantCeiling ∧ ExactReachedCutoffDominance

end LogicLineages.PermittedControl.ActualTraceSignCutoff
