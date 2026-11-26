module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original concrete source forces the actual head of a genuine cons
context to match a top variable's requested type. Matching is a conclusion,
not an erasure premise or a native calibration fact. -/
def OriginalSourceTopDomain : Prop :=
 ∀ (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed raw typ parameter context gamma extended domain : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter ⊓
    (graph1 OriginalRawSyntaxTransport.variableConstructor raw (numeral 0) ⊓
    (graph2 InternalPairing.pairing packed typ raw ⊓
    (graph2 InternalPairing.pairing parameter context extended ⊓
     graph2 InternalListCodec.consCode extended domain gamma)))).imp
   (equal domain typ)))

/-- Full top-variable collapse in an arbitrary actual cons context. The
removed domain is arbitrary at entry and is forced by SAME-final original
typing. The original positive certificate determines the bottom target;
both raw erasures, their equality, and ORIGINAL rank drop are conclusions. -/
def OriginalArbitraryDomainTopCollapse : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (context : Nat) (tau : Ty)
 (source target witness gamma extended packed raw domain erasedSource erasedTarget : OTerm alpha),
 Nonempty (Derivation body Delta
  ((OriginalErasureCertificateContinuation.Premise p H G W context tau
     source target witness gamma extended packed raw domain (numeral 0) ⊓
    (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
     graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)).imp
   (equal domain (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) ⊓
    OriginalVariableErasureCertificate.RawResult tau source target gamma extended
     erasedSource erasedTarget)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.TopDomainTargets
