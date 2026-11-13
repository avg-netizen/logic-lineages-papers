module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationCoreProof
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
/-- Pays every semantic and source prerequisite of forward application
congruence from the genuine smaller-payload IH. Right projections here are
operational witnesses only and will be queried by the enclosing wrapper. -/
theorem atOutputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
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
 Nonempty (Derivation body Delta
  (Domain p H G W out parameter ⊓
   (AdmittedPair (baseRepresentative p H G W) H G (member p H G W) W fn fOut parameter ⊓
    (AdmittedPair (baseRepresentative p H G W) H G (member p H G W) W arg aOut parameter ⊓
     applicationConstructors arrow d e fRaw aRaw fOut aOut out)))) := by
 have fields := OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow d e fp ap fn arg input hc
 have hd := andLeft hp
 have children := EvaluatorKeyApplicationDomainProof.actualApplicationDomain p H G W body alpha Delta
  input parameter d e fn arg hd fields
 have dfn := andLeft children
 have darg := andRight children
 have ifn := EvaluatorKeyCanonicalPreservationBindingProof.belowPayloadApply p H G W P q fp fn fOut parameter
  hb hfl (pairRight fn arrow fp (andLeft (andRight hc))) (andIntro dfn hf)
 have iarg := EvaluatorKeyCanonicalPreservationBindingProof.belowPayloadApply p H G W P q ap arg aOut parameter
  hb hal (pairRight arg d ap (andLeft (andRight (andRight hc)))) (andIntro darg ha)
 have afn := EvaluatorKeyOtherDomainProof.admitted p H G W fn fOut parameter dfn (andLeft ifn) (andRight ifn)
 have aarg := EvaluatorKeyOtherDomainProof.admitted p H G W arg aOut parameter darg (andLeft iarg) (andRight iarg)
 have tf := EvaluatorKeyCanonicalPreservationTypeProof.outputType p H G W P fn fOut parameter arrow dfn hf
  (pairLeft fn arrow fp (andLeft (andRight hc)))
 have ta := EvaluatorKeyCanonicalPreservationTypeProof.outputType p H G W P arg aOut parameter d darg ha
  (pairLeft arg d ap (andLeft (andRight (andRight hc))))
 have hout := OriginalLambdaTraversalInternalApplicationProof.applicationForward
  (OriginalLambdaTraversalSelection.leaf (refined p H G W P).base (refined p H G W P).window)
  input d e fn arg parameter fOut aOut out fields hf ha (andRight hp)
 have co := EvaluatorKeyCanonicalPreservationApplicationSupportProof.rebuiltConstructors arrow d e fOut aOut fRaw aRaw out
  (andLeft hc) tf ta hfr har hout
 have dout := EvaluatorKeyCanonicalDomainProof.actualCanonicalDomain p H G W P body alpha Delta input out parameter hd (andRight hp)
 exact andIntro dout (andIntro afn (andIntro aarg co))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationCoreProof
