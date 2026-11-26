module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.CoreCompose
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.ReflexivityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ReflexivitySupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Retained actual reflexivity, transported between real cons occurrences. -/
theorem current {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) (raw index fuel : Term ctx)
 (hv : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag raw)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue I.previous.current.ctag I.previous.current.atag raw raw)
   (RawCumulativeLogical.certificate I.previous.current.ctag
    I.previous.previous.previous.previous.previous.reflexivityTag raw))) := by
 let J := I.previous.previous.previous.previous.previous
 obtain ⟨hr⟩ := ReflexivityProof.current p f lhs rhs t old ar x I.previous G raw index fuel hv
 obtain ⟨hretain⟩ := CumulativePropositionalSource.CapabilitySupport.retentionInternal p f lhs rhs t old ar x I index fuel .zero _ _
 have hc := Hilbert.Local.mp (.base hretain) hr
 obtain ⟨he⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p J.consTag I.previous.current.ctag 2
  HistoryCodec.cons J.hc I.previous.current.h_ctag ctx
  (Continuation20261114.RawReflexivity.lineCall J.reflexivityTag raw ::ᵥ .zero ::ᵥ nil)
 exact RebaseProof.coreCode _ G I.currentK.coreTag index fuel _ _ _ (.base he) hc
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ReflexivitySupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ReflexivitySupport
