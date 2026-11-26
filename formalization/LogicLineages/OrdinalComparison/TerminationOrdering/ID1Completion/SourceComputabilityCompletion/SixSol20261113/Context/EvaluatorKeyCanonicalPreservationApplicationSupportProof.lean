module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Genuine rebuilt raw application, retaining actual output child types. -/
theorem rebuiltConstructors (arrow d e fn arg fp ap out : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
 (hfl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)))
 (hal : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d arg)))
 (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
 (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
 (hc : Nonempty (Derivation body Delta (graph4 application out d e fn arg))) :
 Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg out)) := by
 exact andIntro ht (andIntro (reconstructPair fn arrow fp hfl hfr)
  (andIntro (reconstructPair arg d ap hal har)
   (InternalApplicationCertificateConstructorsSupportProof.applicationForward d e fn arg fp ap out hfr har hc)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
