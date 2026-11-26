module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeAlgebra
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalInterface
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.TruthValidity
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.DNECore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph GraphInterface GraphValues
/-- Original DNE construction, with every logical singleton and the fixed
reflexivity certificate derived in the actual selected logical source. -/
theorem current {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t (CurrentQuantifierLogicalSource.selectedOld rawOld) ar x)
 (N : LogicalInterface.Nodes p) (G : List (Formula ctx)) (a index fuel : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval a)) :
 let J := RuntimeTags.tags I (N.singletonTag false) (N.singletonTag true)
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (iv J (nv J (nv J a)) a) (dneValue J a))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let J := RuntimeTags.tags I (N.singletonTag false) (N.singletonTag true)
 let R : Term ctx := TruthSupport.truthCode
 let A := nv J (nv J a)
 obtain ⟨hR⟩ := TruthValidity.valid p f lhs rhs t old ar x I G
 obtain ⟨hna⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G a 0 ha
 obtain ⟨hA⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G (nv J a) 0 hna
 obtain ⟨hnR⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G R 0 hR
 obtain ⟨hnnR⟩ := ValiditySupport.negation p f lhs rhs t old ar x I G (nv J R) 0 hnR
 obtain ⟨hQA⟩ := ValiditySupport.implication p f lhs rhs t old ar x I G (nv J (nv J R)) A hnnR hA
 obtain ⟨hB⟩ := ValiditySupport.implication p f lhs rhs t old ar x I G (nv J a) (nv J R) hna hnR
 obtain ⟨hC⟩ := ValiditySupport.implication p f lhs rhs t old ar x I G R a hR ha
 have hg1 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.guards false I.currentK.fval (nv J R) (nv J a)) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hnR) hna
 obtain ⟨hc1⟩ := LogicalInterface.logical p f lhs rhs t rawOld ar x I N false G (nv J R) (nv J a) index fuel hg1
 have hgK : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.guards false I.currentK.fval A (nv J (nv J R)) A) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hA) hnnR
 obtain ⟨hK⟩ := AlgebraSupport.singleton p f lhs rhs t old ar x (RuntimeRebase.shared p f lhs rhs t old ar x I)
  (GorbowPRNumeralCalculation.Theory p) (fun _ h => h) G false A (nv J (nv J R)) A index fuel hgK
 obtain ⟨hfirst⟩ := RuntimeAlgebra.compose p f lhs rhs t old ar x I (N.singletonTag false) (N.singletonTag true) G
  A (iv J (nv J (nv J R)) A) (iv J (nv J a) (nv J R)) _ _ index fuel hA hQA hB hc1 hK
 have hg2 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.guards false I.currentK.fval a R) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) ha) hR
 obtain ⟨hc2⟩ := LogicalInterface.logical p f lhs rhs t rawOld ar x I N false G a R index fuel hg2
 obtain ⟨hsecond⟩ := RuntimeAlgebra.compose p f lhs rhs t old ar x I (N.singletonTag false) (N.singletonTag true) G
  A (iv J (nv J a) (nv J R)) (iv J R a) _ _ index fuel hA hB hC hc2 hfirst
 obtain ⟨htruth⟩ := TruthSupport.certificate p f lhs rhs t old ar x I G index fuel
 obtain ⟨hlift⟩ := RuntimeAlgebra.lift p f lhs rhs t old ar x I (N.singletonTag false) (N.singletonTag true) G
  R A _ index fuel hR hA htruth
 exact RuntimeAlgebra.under p f lhs rhs t old ar x I (N.singletonTag false) (N.singletonTag true) G
  A R a _ _ index fuel hA hR ha hsecond hlift
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.DNECore
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.DNECore
