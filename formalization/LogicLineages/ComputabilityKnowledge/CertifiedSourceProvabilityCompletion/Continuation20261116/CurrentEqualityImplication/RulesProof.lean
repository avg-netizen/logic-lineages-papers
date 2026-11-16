module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.RulesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem lift {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (A B code index fuel : Term ctx)
 (hA : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval A)))
 (hB : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval B)))
 (hcode : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel A code))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (impValue I.previous.current.ctag I.previous.current.atag B A) (liftCertificate I A B code))) := by
 let U := GorbowPRNumeralCalculation.Theory p
 obtain ⟨hA⟩ := hA
 obtain ⟨hB⟩ := hB
 obtain ⟨hcode⟩ := hcode
 have hg : Hilbert.Local U ctx G (UniformClosedPropositional.guards false I.currentK.fval A B A) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hA) hB
 obtain ⟨hk⟩ := AlgebraSupport.singleton p installed lhs rhs t old a x I U (fun _ h => h) G false A B A index fuel hg
 obtain ⟨hout⟩ := AlgebraSupport.one p installed lhs rhs t old a x I U (fun _ h => h) G
  A (impValue I.previous.current.ctag I.previous.current.atag B A) _ code index fuel hk hcode
 exact AlgebraSupport.acceptedOfCore p installed lhs rhs t old a x I U (fun _ h => h) G _ _ index fuel hout
theorem mPUnder {arity k ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (G : List (Formula ctx)) (P Q R hi ha index fuel : Term ctx)
 (hP : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentS.fval P)))
 (hQ : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentS.fval Q)))
 (hR : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentS.fval R)))
 (hhi : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (impValue I.previous.current.ctag I.previous.current.atag P
   (impValue I.previous.current.ctag I.previous.current.atag Q R)) hi)))
 (hha : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (impValue I.previous.current.ctag I.previous.current.atag P Q) ha))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (impValue I.previous.current.ctag I.previous.current.atag P R) (mpUnderCertificate I P Q R hi ha))) := by
 let U := GorbowPRNumeralCalculation.Theory p
 obtain ⟨hP⟩ := hP
 obtain ⟨hQ⟩ := hQ
 obtain ⟨hR⟩ := hR
 obtain ⟨hhi⟩ := hhi
 obtain ⟨hha⟩ := hha
 have hg : Hilbert.Local U ctx G (UniformClosedPropositional.guards true I.currentS.fval P Q R) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hP)
   (.mp (.mp (.base (.logical (.andIntro _ _))) hQ) hR)
 let J := I.previous.current
 obtain ⟨hs⟩ := AlgebraSupport.singleton p installed lhs rhs t old a x I U (fun _ h => h) G true P Q R index fuel hg
 obtain ⟨hfirst⟩ := AlgebraSupport.one p installed lhs rhs t old a x I U (fun _ h => h) G
  (impValue J.ctag J.atag P (impValue J.ctag J.atag Q R))
  (impValue J.ctag J.atag (impValue J.ctag J.atag P Q) (impValue J.ctag J.atag P R))
  _ hi index fuel hs hhi
 obtain ⟨hout⟩ := AlgebraSupport.one p installed lhs rhs t old a x I U (fun _ h => h) G
  (impValue J.ctag J.atag P Q) (impValue J.ctag J.atag P R) _ ha index fuel hfirst hha
 exact AlgebraSupport.acceptedOfCore p installed lhs rhs t old a x I U (fun _ h => h) G _ _ index fuel hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.RulesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.RulesProof
