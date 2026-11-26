module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Membership

def ActualContainsNative : Prop := ∀ (code needle : Nat),
  evaluate contains (List.Vector.ofFn ![code,needle]) =
    (decide (needle ∈ (NumberedMultisetNumeric.decodeNumbers code).getD [])).toNat

/-- Only genuine original list/candidate values are compiled; no internal
correctness or desired compatibility rule is stored in these witnesses. -/
def ActualLeafSelection : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ L D : Program 2, ListCalibrated n arity L ∧ CandidateCalibrated n arity D

def ActualClassCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (T L D : Program 2),
  TargetCalibrated n arity T → ListCalibrated n arity L → CandidateCalibrated n arity D →
  OriginalTransparentMinimum.ClassTestCalibrated n arity (classTest T L D)

/-- Independent symbolic recursion laws at literal nil/cons codes. No native
calibration, source decoding or parent semantic equality is a premise. -/
def ActualInternalContains : Prop :=
  (∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (needle : OTerm alpha),
    Nonempty (Derivation body Delta (graph2 contains (numeral 0) (numeral 0) needle))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (code head tail needle : OTerm alpha),
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
    Nonempty (Derivation body Delta (equal head needle)) →
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) code needle))) ∧
  (∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (code head tail needle out : OTerm alpha),
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)) →
    Nonempty (Derivation body Delta (equal head needle).not) →
    Nonempty (Derivation body Delta (graph2 contains out tail needle)) →
    Nonempty (Derivation body Delta (graph2 contains out code needle)))

/-- Actual L/D graphs, actual original target acceptance and actual literal
membership suffice to introduce this exact new class Program internally. -/
def ActualInternalClassIntroduction : Prop :=
  ∀ (T L D : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed candidate parameter list needle : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) candidate parameter)) →
  Nonempty (Derivation body Delta (graph2 L list seed parameter)) →
  Nonempty (Derivation body Delta (graph2 D needle candidate parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)) →
  Nonempty (Derivation body Delta (graph3 (classTest T L D) (numeral 1) seed candidate parameter))

/-- Genuine all-vector equality and the entire accepted prior package at the
explicitly NEW initial representative tuple. This is not internal L/D
correctness, E-to-primary completeness or calibrated compatibility. -/
def ActualRetainedInstallation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W L D : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  ListCalibrated n arity L → CandidateCalibrated n arity D →
  OriginalTransparentMinimum.NativePreparation n arity p H G
      (classTest (OriginalTypedDecoder.target H G) L D) ∧
  OriginalTransparentMinimum.Retained n arity p H G W
      (classTest (OriginalTypedDecoder.target H G) L D)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipTargets
