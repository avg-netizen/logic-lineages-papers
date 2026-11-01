module
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateProbeCode : Prop :=
  Primrec₂ positiveVariableHeadCode ∧ Primrec₂ encodedMultivariateProbe ∧
  (∀ cap i : Nat, positiveVariableHeadCode cap i=rawNoteEncode (positiveVariableHead cap i).1) ∧
  ∀ (cap : Nat) (E : MultivariatePositiveExpr),
    encodedMultivariateProbe cap (multivariatePositiveEncode E)=
      positiveExprEncode (multivariatePositiveProbe cap E)

/-- Complete uniform multivariate semantic identity algorithm, but only a
supplier for paper07 thm:identity: its literal NF and weighted-Phi witness
clauses must not be inferred from this separate finite-probe decision. -/
def MultivariateIdentityDecision : Prop :=
  Computable₂ encodedMultivariateIdentity ∧
  Computable₂ encodedMultivariateProbeCounterInput ∧
  Computable (fun p : Nat × Nat × Nat => encodedMultivariateCounterWeight p.1 p.2.1 p.2.2) ∧
  ∀ (d : Nat) (E F : MultivariatePositiveExpr),
    multivariatePositiveValid d E → multivariatePositiveValid d F →
    let n := multivariatePositiveEncode E
    let m := multivariatePositiveEncode F
    (encodedMultivariateIdentity n m=true ↔
      ∀ ρ : Nat → Nat, (∀ i : Nat, i<d → 0<ρ i) →
        actualMultivariatePositiveEval E ρ=actualMultivariatePositiveEval F ρ) ∧
    (encodedMultivariateIdentity n m=false →
      (∀ i : Nat, 0<encodedMultivariateCounterWeight n m i) ∧
      actualMultivariatePositiveEval E (encodedMultivariateCounterWeight n m)≠
        actualMultivariatePositiveEval F (encodedMultivariateCounterWeight n m))

end LogicLineages.OrdinalComparison.Targets
