module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.MPUnderProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem exactMPUnder : Targets.InternalMPUnder := by
 intro installed lhs rhs k t old a baseX pF pR I ctx G P Q R hi ha index fuel hP hQ hR hhi hha
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨hP⟩ := hP
 obtain ⟨hQ⟩ := hQ
 obtain ⟨hR⟩ := hR
 obtain ⟨hhi⟩ := hhi
 obtain ⟨hha⟩ := hha
 have hg : Hilbert.Local U ctx G (UniformClosedPropositional.guards true I.currentS.fval P Q R) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hP)
   (.mp (.mp (.base (.logical (.andIntro _ _))) hQ) hR)
 let J := I.previous.current
 obtain ⟨hs⟩ := AlgebraSupport.singleton p installed lhs rhs t old a _ I U hTU G true P Q R index fuel hg
 obtain ⟨hfirst⟩ := AlgebraSupport.one p installed lhs rhs t old a _ I U hTU G
  (impValue J.ctag J.atag P (impValue J.ctag J.atag Q R))
  (impValue J.ctag J.atag (impValue J.ctag J.atag P Q) (impValue J.ctag J.atag P R))
  _ hi index fuel hs hhi
 obtain ⟨hout⟩ := AlgebraSupport.one p installed lhs rhs t old a _ I U hTU G
  (impValue J.ctag J.atag P Q) (impValue J.ctag J.atag P R) _ ha index fuel hfirst hha
 exact AlgebraSupport.acceptedOfCore p installed lhs rhs t old a _ I U hTU G _ _ index fuel hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.MPUnderProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.MPUnderProof
