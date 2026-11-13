module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableDichotomyTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual erased Objects either coincide with strict rank drop between the
original endpoints, or carry a new ORIGINAL positive source certificate.
The certificate existential uses the unchanged selected source at this tuple. -/
def Result {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (context : Nat)
    (source target erasedSource erasedTarget : OTerm alpha) : Formula alpha :=
  (equal erasedSource erasedTarget ⊓
    OriginalVariableErasureCertificate.OriginalRankDrop source target) ⊔
    Erasure.VariableSourceErasureTargets.CertificateWitness p H G W P context
      erasedSource erasedTarget

/-- ALL original variable indices and arbitrary actual removed domains. The
input is the literal original positive certificate, actual cons context and
actual Object erasures. No input recognition, output typing, fold fixedness,
canonical cancellation or certificate-transformer law is supplied. -/
def ActualOriginalVariableSourceErasureDichotomy : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalErasureCertificateContinuation.Premise
        (Erasure.VariableSourceErasureTargets.preparedSeed p H G W P) H G W context tau
        source target witness gamma extended packed raw domain index ⊓
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
        graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)).imp
      Result p H G W P context source target erasedSource erasedTarget))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.OriginalVariableDichotomyTargets
