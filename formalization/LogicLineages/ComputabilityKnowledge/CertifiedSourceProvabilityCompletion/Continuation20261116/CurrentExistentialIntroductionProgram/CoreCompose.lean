module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.RulesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.CoreCompose
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Literal K-lift followed by S's two MP steps, at the unchanged current CORE. -/
theorem compose {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) (P Q R hqr hpq index fuel : Term ctx)
 (hP : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval P))
 (hQ : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval Q))
 (hR : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval R))
 (hq : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel
  (impValue I.previous.current.ctag I.previous.current.atag Q R) hqr))
 (hp : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel
  (impValue I.previous.current.ctag I.previous.current.atag P Q) hpq)) :
 let J := RuntimeRebase.shared p f lhs rhs t old ar x I
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (impValue I.previous.current.ctag I.previous.current.atag P R)
   (mpUnderCertificate J P Q R
    (liftCertificate J (impValue I.previous.current.ctag I.previous.current.atag Q R) P hqr) hpq))) := by
 let J := RuntimeRebase.shared p f lhs rhs t old ar x I
 obtain ⟨hQR⟩ := CurrentEqualityImplication.GuardProof.implication p f lhs rhs t old ar x J G false Q R hQ hR
 obtain ⟨hl⟩ := CurrentEqualityImplication.RulesProof.lift p f lhs rhs t old ar x J G
  (impValue I.previous.current.ctag I.previous.current.atag Q R) P hqr index fuel ⟨hQR⟩ ⟨hP⟩ ⟨hq⟩
 have hlc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hl
 obtain ⟨hm⟩ := CurrentEqualityImplication.RulesProof.mPUnder p f lhs rhs t old ar x J G
  P Q R _ hpq index fuel ⟨hP⟩ ⟨hQ⟩ ⟨hR⟩ ⟨hlc⟩ ⟨hp⟩
 exact ⟨Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hm⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.CoreCompose
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.CoreCompose
