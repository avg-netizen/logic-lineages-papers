module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.DNECore
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.AllCore
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.InstanceValidity
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphRule
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuleCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph GraphInterface GraphValues GraphRule
theorem current {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar x)
 (N : LogicalInterface.Nodes p) (G : List (Formula ctx)) (a w index fuel : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.currentK.fval I.previous.previous.current.vtag a w)) :
 let J := RuntimeTags.tags I (N.singletonTag false) (N.singletonTag true)
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (iv J (instanceValue J a w) (FixedFormulaSubstitution.unaryValue J.ctag 11 a)) (ruleValue J a w))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let J := RuntimeTags.tags I (N.singletonTag false) (N.singletonTag true)
 let R := RuntimeRebase.shared p f lhs rhs t old ar x I
 let V := R.previous.previous.current.toDispatcherInstallation.toInstallation
 let P := FixedFormulaSubstitution.unaryValue J.ctag 10 (nv J a)
 let inst := instanceValue J a w
 have hA := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hg
 obtain ⟨hP⟩ := ValiditySupport.universalNegation p f lhs rhs t old ar x I G a hA
 obtain ⟨hI⟩ := InstanceValidity.valid p V G a w hg
 obtain ⟨hnP⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G P 0 hP
 obtain ⟨hnnP⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G (nv J P) 0 hnP
 obtain ⟨hnI⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G inst 0 hI
 obtain ⟨hEx⟩ := ValiditySupport.existential p f lhs rhs t old ar x I G a hA
 obtain ⟨hinst⟩ := AllCore.negated p f lhs rhs t old ar x I G a w index fuel hg
 obtain ⟨hdne⟩ := DNECore.current p f lhs rhs t rawOld ar x I N G P index fuel hP
 obtain ⟨hbridge⟩ := RuntimeAlgebra.compose p f lhs rhs t old ar x I (N.singletonTag false) (N.singletonTag true) G
  (nv J (nv J P)) P (nv J inst) _ _ index fuel hnnP hP hnI hinst hdne
 have hcg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.guards false I.currentK.fval (nv J P) inst) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hnP) hI
 obtain ⟨hc⟩ := LogicalInterface.logical p f lhs rhs t rawOld ar x I N false G (nv J P) inst index fuel hcg
 obtain ⟨hnegative⟩ := AlgebraSupport.one p f lhs rhs t old ar x I (GorbowPRNumeralCalculation.Theory p)
  (fun _ h => h) G (iv J (nv J (nv J P)) (nv J inst)) (iv J inst (nv J P)) _ _ index fuel hc hbridge
 obtain ⟨hdual⟩ := LogicalInterface.logical p f lhs rhs t rawOld ar x I N true G a .zero index fuel hA
 exact RuntimeAlgebra.compose p f lhs rhs t old ar x I (N.singletonTag false) (N.singletonTag true) G
  inst (nv J P) (FixedFormulaSubstitution.unaryValue J.ctag 11 a) _ _ index fuel hI hnP hEx hdual hnegative
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuleCore
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuleCore
