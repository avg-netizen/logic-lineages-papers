module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataTargets
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficient
open OrdinalComparison.CommonHeadLargeGuards (maskCoefficient)
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm encodeTerm groupRaw groupTyped)
open ActualRawCanonicalNodeMetadata (activeLabelCode classFlagsCode)
open ActualFullValueMaximalMetadata (doubledWeight weights maximalCoefficient)
open ActualFullLabelPairGuards (Answer)

def doubledCode (t : RawTerm) : Int :=
  if t.2.1 = 1 then 2 * t.1 else if t.2.1 = 2 then t.1 else 0

def weightsCode (ts : List RawTerm) : List Int :=
  ts.filterMap (fun t => (activeLabelCode t).map (fun _ => doubledCode t))

def coefficientCode (ts : List RawTerm) (answers : List Nat) : Int :=
  maskCoefficient (weightsCode ts) (classFlagsCode ts answers)

def ExactRawCanonicalWeightTape : Prop :=
  (∀ t : WeightedOperand, doubledCode (encodeTerm t) = doubledWeight t) ∧
  ∀ ts : List WeightedOperand, weightsCode (ts.map encodeTerm) = weights ts

def ExactRawCanonicalCoefficient : Prop :=
  (∀ (ts : List WeightedOperand) (answers : List Answer),
    coefficientCode (ts.map encodeTerm) (answers.map Answer.code) = maximalCoefficient ts answers) ∧
  ∀ (ts : List WeightedOperand) (answers : List Answer),
    coefficientCode (groupRaw (ts.map encodeTerm)) (answers.map Answer.code) =
      maximalCoefficient (groupTyped ts) answers

def ExactRawCanonicalCoefficientEffectivity : Prop :=
  Primrec doubledCode ∧ Primrec weightsCode ∧ Primrec₂ coefficientCode

def FullActualRawCanonicalNodeCoefficient : Prop :=
  ExactRawCanonicalWeightTape ∧ ExactRawCanonicalCoefficient ∧ ExactRawCanonicalCoefficientEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficient
