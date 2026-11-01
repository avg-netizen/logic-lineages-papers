module
public import LogicLineages.OrdinalComparison.MultivariateCollectedDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def MultivariateCollectedStorageInjective : Prop :=
  Function.Injective multivariateCollectedCode ∧ Function.Injective multivariateCollectedTagsCode

def MultivariateCollectedAdditiveSemantics : Prop :=
  (∀ (A B : MultivariateCollectedNF) (rho : Nat → Nat),
    actualMultivariateCollectedValue (multivariateCollectedAdd A B) rho=
      actualMultivariateCollectedValue A rho+actualMultivariateCollectedValue B rho) ∧
  (∀ (i a : Nat) (rho : Nat → Nat),
    multivariateCoefficientValue (multivariateVariableCoefficients i a) rho=a*rho i)

/-- Actual recursive fresh-input shape of the NORMALIZER OUTPUT, not an
extra well-formedness premise on a source or supplied normal form. -/
def MultivariateCollectedProbeShape : Prop :=
  ∀ (d cap : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    multivariatePositiveEncode E≤cap →
      MultivariateProbeNFShape d cap (collectedPositiveNormalize (multivariatePositiveProbe cap E))

def MultivariateCollectedDecodeSemantics : Prop :=
  ∀ (d cap : Nat) (A : CollectedPositiveNF), MultivariateProbeNFShape d cap A →
    ∀ rho : Nat → Nat,
      actualMultivariateCollectedValue (decodeMultivariateCollected cap A) rho=
        interpretedCollectedEval (positiveRetractedHead cap rho) A 0

/-- Value preservation of the actual recursively collected multivariate
dictionary, for every original valuation. This is a SOURCE SUPPLIER ONLY:
storage canonicality, cap independence, uniform computability and complete
NF equality remain required before promoting the entire identity theorem. -/
def MultivariateCollectedSourceSemantics : Prop :=
  ∀ (d cap : Nat) (E : MultivariatePositiveExpr), multivariatePositiveValid d E →
    multivariatePositiveEncode E≤cap → ∀ rho : Nat → Nat,
      actualMultivariateCollectedValue (multivariateCollectedNormalizeAt cap E) rho=
        actualMultivariatePositiveEval E rho

end LogicLineages.OrdinalComparison.Targets
