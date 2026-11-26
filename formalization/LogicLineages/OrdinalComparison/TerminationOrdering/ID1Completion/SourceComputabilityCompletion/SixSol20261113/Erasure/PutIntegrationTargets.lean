module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalPositiveCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutIntegration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Install the accepted literal PUT leaf once, after the original transparent
source decoder and before the unchanged mixed/active-kernel final pipeline. -/
def seed (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  SixSol20261112.Erasure.PutRoot.refineInputs
    (OriginalTransparentDecoderSelection.transparentInputs H G W p)
def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
  SixSol20261112.Integration.preparedKernelFinalInputs (seed p H G W) H G W P
def finalData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
  SixSol20261112.Integration.preparedKernelFinalData (seed p H G W) H G W P

def Fields {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3)
    (s t cert parameter typ raw head base label : OTerm alpha) : Formula alpha :=
  graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P))
      (numeral 1) s parameter ⊓
    (graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base ⊓
        (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label ⊓
          graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label)))

/-- Actual final guarded W, not only raw PUT leaf acceptance. The target,
source/target validity, constructor/neutral/spine guards and selected nil-path
checker must be paid internally from the original source rule geometry. -/
def ActualFinalPutStep : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ raw head base label : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Fields p H G W P s t cert parameter typ raw head base label).imp
      (stepAccepted (finalData p H G W P) (finalInputs p H G W P).oldStep
        s t cert parameter)))

/-- Retain the ENTIRE prepared active-kernel package for this same seed,
including all previously accepted native/global properties. -/
def ActualPutPreparation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalMixedPrepared.Properties n arity (seed p H G W) H G W P

/-- Literal original positive source certificate for actual fold outputs of
the source and literal PUT target, retaining one final tuple and parameter.
No oldStep/W acceptance, target typing or canonical fixedness is supplied. -/
def ActualFinalPutObjectCertificate : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (context : Nat)
    (s t cert parameter typ raw head base label gamma x y quotient entry path first second : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Fields p H G W P s t cert parameter typ raw head base label ⊓
      ((graph1 (finalInputs p H G W P).window (numeral 1) (numeral context) ⊓
        graph2 InternalPairing.pairing parameter (numeral context) gamma) ⊓
      ((InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) x s parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) y t parameter) ⊓
      ((graph3 edgeCode quotient s t cert ⊓
        (graph2 InternalPairing.pairing entry y quotient ⊓
          graph2 InternalListCodec.consCode path entry (numeral 0))) ⊓
        (graph2 InternalPairing.pairing first gamma x ⊓ graph2 InternalPairing.pairing second gamma y))))).imp
      (InternalAccessibilityRules.certificate (GlobalSourcePackage.source (finalInputs p H G W P))
        false context first second path)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutIntegration
