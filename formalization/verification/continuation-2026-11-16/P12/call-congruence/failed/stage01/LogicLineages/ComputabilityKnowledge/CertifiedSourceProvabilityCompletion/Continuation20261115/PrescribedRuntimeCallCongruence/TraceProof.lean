module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.CertificateTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open PrescribedRuntimeEquality
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114

theorem exactTraces : Targets.InternalPrescribedTraces := by
 intro arity k p installedFormula lhs rhs arithmeticTerm old arithmetic x I ctx n tag args others codes
 let J := tags I
 obtain ⟨htv⟩ := ValueTraceProof.tuple (ctx := ctx) p J I.current.h_ctag I.current.h_atag args.toList
 obtain ⟨hcv⟩ := ValueTraceProof.call (ctx := ctx) p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hnumeral tag args
 obtain ⟨htc⟩ := CertificateTraceProof.tuple (ctx := ctx) p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hmp I.current.h_constructor
  I.previous.previous.previous.previous.hc I.previous.previous.previous.previous.hreflexivity n args others codes
 obtain ⟨hcc⟩ := CertificateTraceProof.call (ctx := ctx) p J I.current.h_ctag I.current.h_atag
  I.previous.previous.previous.previous.hmp I.current.h_constructor
  I.previous.previous.previous.previous.hc I.previous.previous.previous.previous.hreflexivity
  I.previous.previous.previous.previous.hnumeral tag args others codes
 exact ⟨Derivation.mp (.mp (.logical (.andIntro _ _)) htv)
  (.mp (.mp (.logical (.andIntro _ _)) hcv)
   (.mp (.mp (.logical (.andIntro _ _)) htc) hcc))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TraceProof
