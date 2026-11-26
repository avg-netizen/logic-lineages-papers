module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114

theorem internalEdge : Targets.InternalEdge := by
  intro n arity body alpha Delta source target param tyA codeA tyB codeB ctx rest hs ht hp
  have hf := TypedPrimaryEdge.InternalProof.internalFactor (structural n arity) body alpha Delta
    source target param tyA tyB (pairLeft source tyA codeA hs) (pairLeft target tyB codeB ht)
  constructor
  · intro h
    have hc := hf.mp h
    exact andIntro (andLeft hc)
      (CoreProof.structuralForward n arity source target param tyA codeA tyB codeB ctx rest hs ht hp (andRight hc))
  · intro h
    exact hf.mpr (andIntro (andLeft h)
      (CoreProof.structuralBackward n arity source target param tyA codeA tyB codeB ctx rest hs ht hp (andRight h)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
