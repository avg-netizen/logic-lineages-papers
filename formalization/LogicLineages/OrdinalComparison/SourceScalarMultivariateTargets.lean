module
public import LogicLineages.OrdinalComparison.SourceScalarMultivariateDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateSourceBridge.Targets
open Source.ForwardTranslation

def RawOmegaNoFinitePart : Prop :=
  (∀ a b : ONote, RawWithoutFinitePart a → RawWithoutFinitePart b →
    RawWithoutFinitePart (rawNaturalSum a b)) ∧
  (∀ b : ONote, RawWithoutFinitePart (rawNaturalProduct profileOmegaNote.1 b)) ∧
  (∀ a : ONote, RawWithoutFinitePart a → a.repr=0 ∨ Order.IsSuccLimit a.repr)

/-- The actual omega-natural-product head is a LIMIT, not merely infinite.
This is paid for every source closed-positive syntax, with no limit premise. -/
def SourceScalarFixedLimit : Prop :=
  ∀ c : ClosedPositive,
    Order.IsSuccLimit (scalarHeadNote c).1.repr ∧
    (scalarHeadNote c).1.repr<epsilonZero ∧ (scalarHeadNote c).1.repr=fixedHead c

def SourceScalarMultivariateAdapter : Prop :=
  (∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
    multivariatePositiveEncode (scalarToMultivariate index s)=scalarCode index s) ∧
  (∀ (ι : Type) (index : ι → Nat) (d : Nat) (s : Scalar ι),
    scalarVariablesBelow index d s → multivariatePositiveValid d (scalarToMultivariate index s)) ∧
  (∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) (ρ : Nat → Nat),
    actualMultivariatePositiveEval (scalarToMultivariate index s) ρ=s.value (fun x => ρ (index x)))

end LogicLineages.OrdinalComparison.MultivariateSourceBridge.Targets
