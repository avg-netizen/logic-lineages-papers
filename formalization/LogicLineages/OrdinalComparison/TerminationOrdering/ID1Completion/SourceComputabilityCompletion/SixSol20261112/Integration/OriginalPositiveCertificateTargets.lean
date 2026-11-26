module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedFinalErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original atomic computation/constructor geometry for a singleton quotient
path. No typing, membership, non-bottom, spine, or certificate-success law is
supplied. W and both canonical folds use the SAME retained final Data. -/
def StepObjectCertificateFields {alpha : Type}
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat)
    (parameter gamma source typ raw target step x y quotient entry path first second : OTerm alpha) :
    Formula alpha :=
  let f := preparedKernelFinalInputs p H G W P
  let D := preparedKernelFinalData p H G W P
  let Window := graph1 f.window (numeral 1) (numeral context) ⊓
    graph2 InternalPairing.pairing parameter (numeral context) gamma
  let Step := graph2 InternalPairing.pairing source typ raw ⊓
    stepAccepted D f.oldStep source target step parameter
  let Folds := InternalParameterizedCanonicalResultFold.foldGraph D x source parameter ⊓
    InternalParameterizedCanonicalResultFold.foldGraph D y target parameter
  let Codes := graph3 edgeCode quotient source target step ⊓
    (graph2 InternalPairing.pairing entry y quotient ⊓
      graph2 InternalListCodec.consCode path entry (numeral 0))
  let Objects := graph2 InternalPairing.pairing first gamma x ⊓
    graph2 InternalPairing.pairing second gamma y
  Window ⊓ (Step ⊓ (Folds ⊓ (Codes ⊓ Objects)))

/-- Reassemble the literal ORIGINAL positive certificate at the SAME final
source. Endpoint typing, actual type-window membership, full quotient spine
guard and both Gamma/outer typed guards must be derived internally.

This conclusion concerns the supplied actual canonical-fold outputs. It does
not identify them with erasures of previous canonical Objects, which remains
the separate final canonical-cancellation obligation. -/
def ActualPreparedKernelStepObjectCertificate : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat)
    (parameter gamma source typ raw target step x y quotient entry path first second : OTerm alpha),
  Nonempty (Derivation body Delta
    ((StepObjectCertificateFields p H G W P context
      parameter gamma source typ raw target step x y quotient entry path first second).imp
      (InternalAccessibilityRules.certificate
        (GlobalSourcePackage.source (preparedKernelFinalInputs p H G W P)) false
        context first second path)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration
