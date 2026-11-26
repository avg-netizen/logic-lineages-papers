module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CallAlgebraTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallReflexivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem current {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old arithmetic : Program 1) (x : Program 3)
 (I : JointInstallation p f lhs rhs t old arithmetic x)
 (G : List (Formula ctx)) (raw index fuel : Term ctx)
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (RawReflexivityDispatcher.valid I.previous.current.vtag raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag raw raw)
   (reflexivityCertificate (tags I.previous) raw))) := by
 obtain ⟨hc⟩ := PrescribedRuntimeEquality.ReflexivityProof.current p f lhs rhs t old arithmetic x I.previous G raw index fuel hv
 obtain ⟨hretain⟩ := CapabilitySupport.retentionInternal p f lhs rhs t old arithmetic x I index fuel .zero _ _
 have hc := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hretain) hc
 let A := equalValue I.previous.current.ctag I.previous.current.atag raw raw
 let code := reflexivityCertificate (tags I.previous) raw
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier p I.currentK.verifierTag I.currentK.coreTag
  (UniformClosedPropositionalCertificate.checker _ _ _) I.currentK.h_verifierTag I.currentK.h_coreTag index fuel .zero (.add A A) code
 have hf := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hc
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hc) hf⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallReflexivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallReflexivityProof
