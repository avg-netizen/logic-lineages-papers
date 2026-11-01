module
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PositiveVariableHeadSource : Prop :=
  (∀ cap i : Nat,
    Order.IsSuccLimit (positiveVariableHead cap i).1.repr ∧
    (positiveVariableHead cap i).1.repr<epsilonZero ∧
    cap<rawNoteEncode (positiveVariableHead cap i).1 ∧
    positiveVariableHeadIndex cap (positiveVariableHead cap i)=some i) ∧
  (∀ (cap : Nat) (rho : NONote), rawNoteEncode rho.1≤cap →
    positiveVariableHeadIndex cap rho=none) ∧
  (∀ cap i x : Nat, 0<actualProfileHead (positiveVariableHead cap i) x)

/-- Full actual-source embedding and recursive NORMAL-FORM head closure.
Freshness is not checked only on a root or a textual list of initial heads. -/
def MultivariateFreshProbeSource : Prop :=
  (∀ (d cap : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    fixedLimitProfileBelow epsilonZero (multivariatePositiveProbe cap E)) ∧
  (∀ (cap x : Nat) (E : MultivariatePositiveExpr),
    actualFixedLimitProfileEval (multivariatePositiveProbe cap E) x=
      actualMultivariatePositiveEval E (fun i => actualProfileHead (positiveVariableHead cap i) x)) ∧
  (∀ (cap : Nat) (E : MultivariatePositiveExpr), multivariatePositiveEncode E≤cap →
    collectedHeadsSatisfy (PositiveProbeHeadClosure cap)
      (collectedPositiveNormalize (multivariatePositiveProbe cap E)))

/-- No semantic agreement or normal-form closure is an extra premise here:
they must be discharged for the actual source tree and every original valuation. -/
def MultivariateFreshProbeRetraction : Prop :=
  ∀ (d cap : Nat) (E : MultivariatePositiveExpr),
    multivariatePositiveValid d E → multivariatePositiveEncode E≤cap →
    ∀ (ρ : Nat → Nat) (x : Nat),
    interpretedCollectedEval (positiveRetractedHead cap ρ)
      (collectedPositiveNormalize (multivariatePositiveProbe cap E)) x=
        actualMultivariatePositiveEval E ρ

end LogicLineages.OrdinalComparison.Targets
