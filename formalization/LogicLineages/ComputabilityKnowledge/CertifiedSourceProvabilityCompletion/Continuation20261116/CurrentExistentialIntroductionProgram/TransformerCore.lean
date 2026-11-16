module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuleCore
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TransformerCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph GraphInterface GraphValues GraphRule
theorem current {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar x)
 (N : LogicalInterface.Nodes p) (transformTag : Nat)
 (ht : (nodes p)[transformTag]? = some ⟨3,program⟩)
 (G : List (Formula ctx)) (a w inputCode index fuel : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedInstanceRecognizer.guards I.currentK.fval I.previous.previous.current.vtag a w))
 (hi : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (instanceValue (RuntimeTags.tags I (N.singletonTag false) (N.singletonTag true)) a w) inputCode)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (FixedFormulaSubstitution.unaryValue I.previous.current.ctag 11 a)
   (call transformTag (a ::ᵥ w ::ᵥ inputCode ::ᵥ nil)))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let J := RuntimeTags.tags I (N.singletonTag false) (N.singletonTag true)
 obtain ⟨hr⟩ := RuleCore.current p f lhs rhs t rawOld ar x I N G a w index fuel hg
 obtain ⟨hm⟩ := AlgebraSupport.one p f lhs rhs t old ar x I (GorbowPRNumeralCalculation.Theory p)
  (fun _ h => h) G (instanceValue J a w) (FixedFormulaSubstitution.unaryValue J.ctag 11 a) _ inputCode index fuel hr hi
 have hnodes := RuntimeTags.installed I (N.singletonTag false) (N.singletonTag true) (N.hsingle false) (N.hsingle true)
 obtain ⟨hgraph⟩ := GraphProof.graph p (a ::ᵥ w ::ᵥ inputCode ::ᵥ nil) J hnodes transformTag ht
 obtain ⟨hfinal⟩ := RebaseProof.coreCode _ G I.currentK.coreTag index fuel _ _ _
  (.base (Support.equalitySymmetry _ _ hgraph)) hm
 exact AlgebraSupport.acceptedOfCore p f lhs rhs t old ar x I _ (fun _ h => h) G _ _ index fuel hfinal
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TransformerCore
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TransformerCore
