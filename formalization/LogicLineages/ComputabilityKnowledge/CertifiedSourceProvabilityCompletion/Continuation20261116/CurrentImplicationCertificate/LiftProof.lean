module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.AlgebraSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.LiftProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem exactLift : Targets.InternalLift := by
 intro installed lhs rhs k t old a baseX pF pR I ctx G A B code index fuel
 dsimp only
 intro hA hB hcode
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨hA⟩ := hA
 obtain ⟨hB⟩ := hB
 obtain ⟨hcode⟩ := hcode
 have hg : Hilbert.Local U ctx G (UniformClosedPropositional.guards false I.currentK.fval A B A) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hA) hB
 obtain ⟨hk⟩ := AlgebraSupport.singleton p installed lhs rhs t old a _ I U hTU G false A B A index fuel hg
 obtain ⟨hout⟩ := AlgebraSupport.one p installed lhs rhs t old a _ I U hTU G
  A (impValue I.previous.current.ctag I.previous.current.atag B A) _ code index fuel hk hcode
 exact AlgebraSupport.acceptedOfCore p installed lhs rhs t old a _ I U hTU G _ _ index fuel hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.LiftProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.LiftProof
