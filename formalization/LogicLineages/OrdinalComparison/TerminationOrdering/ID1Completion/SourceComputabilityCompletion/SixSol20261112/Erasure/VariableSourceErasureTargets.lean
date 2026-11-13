module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedFinalErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (existsOne)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal seed INSIDE the already checked prepared active-kernel final
tuple. No input field, source Program or certificate domain is selected anew. -/
def preparedSeed (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : GlobalSourcePackage.Inputs :=
  let q := OriginalMixedPrepared.prepared p H G W
  let K := OriginalActiveClassKernel.classTest q H G W P
  let Q := OriginalActiveObservedClass.classTest q H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw K
  OriginalTransparentMinimum.minimumInputs H G Q q

def CertificateMatrix {alpha : Type}
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (source target : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  InternalAccessibilityRules.certificate
    (GlobalSourcePackage.source (Integration.preparedKernelFinalInputs p H G W P)) false
    context (source.relabel Sum.inl) (target.relabel Sum.inl) (.var (.inr 0))

def CertificateWitness {alpha : Type}
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (source target : OTerm alpha) : Formula alpha :=
  existsOne (CertificateMatrix p H G W P context source target)

/-- Original positive source-certificate erasure for a surviving variable.
The ORIGINAL arbitrary old certificate, actual Object erasures and genuine
cons/successor shape are the only input; no recognition, new validity, fold
identity, quotient endpoint or certificate transformation is supplied. -/
def ActualOriginalSurvivingVariableSourceErasure : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index erasedSource erasedTarget : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalErasureCertificateContinuation.Premise (preparedSeed p H G W P) H G W context tau
        source target witness gamma extended packed raw domain (suc index) ⊓
      (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
        graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)).imp
      (OriginalErasureCertificateContinuation.SurvivorResult tau source target gamma extended index erasedSource erasedTarget ⊓
        CertificateWitness p H G W P context erasedSource erasedTarget)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureTargets
