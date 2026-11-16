module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ReflexivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (raw index fuel : Term ctx)
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.current.vtag raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.current.coreTag I.current.verifierTag index fuel (equalValue I.current.ctag I.current.atag raw raw)
   (reflexivityCertificate (tags I) raw))) := by
 obtain ⟨hc⟩ := PrescribedRuntimeEquality.ReflexivityProof.current p f lhs rhs t old arithmetic x I G raw index fuel hv
 let A := equalValue I.current.ctag I.current.atag raw raw
 let code := reflexivityCertificate (tags I) raw
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.current.verifierTag I.current.coreTag
  (UniformClosedRule12Certificate.checker _ _ _) I.current.h_verifier I.current.h_core index fuel .zero (.add A A) code
 have hf := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hc
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hc) hf⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ReflexivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ReflexivityProof
