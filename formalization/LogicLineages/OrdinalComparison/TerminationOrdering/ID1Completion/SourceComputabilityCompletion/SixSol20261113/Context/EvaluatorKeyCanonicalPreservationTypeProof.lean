module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTypeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion EvaluatorKeyPut
open EvaluatorKeyCanonicalInductionDefinitions (C)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem outputType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input out parameter typ : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) out input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ out)) := by
 let r := refined p H G W P
 have hp := EvaluatorKeyDomainClosureSupportProof.factors p H G W input parameter hd
 have hs := EvaluatorKeyCanonicalDomainSupportProof.sourceToLeaf p H G W P input parameter (andRight hp)
 have hi := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window out input typ parameter
  (andIntro (andLeft hp) (andIntro (andIntro hs ht) hc))
 exact andLeft (andRight hi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTypeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTypeProof
