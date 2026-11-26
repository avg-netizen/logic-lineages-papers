module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSemanticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalPreservationInductionDefinitions
open EvaluatorKeyCanonicalInductionDefinitions (C)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : EvaluatorKeyCanonicalPreservationDefinitions.Compatible p H G W)
 (q input out parameter arrow d e fp ap fn arg fOut aOut fRaw aRaw : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
 (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)))
 (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q)))
 (hf : Nonempty (Derivation body Delta (graph2 (C p H G W P) fOut fn parameter)))
 (ha : Nonempty (Derivation body Delta (graph2 (C p H G W P) aOut arg parameter)))
 (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fRaw fOut)))
 (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right aRaw aOut))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 have paid := EvaluatorKeyCanonicalPreservationApplicationCoreProof.atOutputs p H G W P
  q input out parameter arrow d e fp ap fn arg fOut aOut fRaw aRaw hb hp hc hfl hal hf ha hfr har
 have dout := andLeft paid
 have pfn := andLeft (andRight paid)
 have parg := andLeft (andRight (andRight paid))
 have co := andRight (andRight (andRight paid))
 have sin := andRight (EvaluatorKeyDomainClosureSupportProof.factors p H G W input parameter (andLeft hp))
 have sout := andRight (EvaluatorKeyDomainClosureSupportProof.factors p H G W out parameter dout)
 have pair := SixSol20261113.Erasure.EvaluatorConstructorCongruenceProof.actualApplication
  (baseRepresentative p H G W) H G (member p H G W) W compat body alpha Delta
  input out fn fOut arg aOut arrow d e fp fRaw ap aRaw parameter sin sout hc co pfn parg
 exact andIntro dout (andRight (andRight pair))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSemanticProof
