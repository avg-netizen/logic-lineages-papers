module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeTags
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.CoreCompose
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphValues
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeAlgebra
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph GraphInterface GraphValues
variable {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (contra dual : Nat) (G : List (Formula ctx))
theorem lift (A B code index fuel : Term ctx)
 (hA : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval A))
 (hB : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval B))
 (hc : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel A code)) :
 let J := RuntimeTags.tags I contra dual
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (iv J B A) (liftValue J A B code))) := by
 obtain ⟨h⟩ := CurrentEqualityImplication.RulesProof.lift p f lhs rhs t old ar x
  (RuntimeRebase.shared p f lhs rhs t old ar x I) G A B code index fuel ⟨hA⟩ ⟨hB⟩ ⟨hc⟩
 exact ⟨Hilbert.Local.mp (.base (.logical (.andLeft _ _))) h⟩

theorem under (P Q R hi ha index fuel : Term ctx)
 (hP : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval P))
 (hQ : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval Q))
 (hR : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval R))
 (hhi : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel
  (iv (RuntimeTags.tags I contra dual) P (iv (RuntimeTags.tags I contra dual) Q R)) hi))
 (hha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel
  (iv (RuntimeTags.tags I contra dual) P Q) ha)) :
 let J := RuntimeTags.tags I contra dual
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (iv J P R) (mpUnderValue J P Q R hi ha))) := by
 obtain ⟨h⟩ := CurrentEqualityImplication.RulesProof.mPUnder p f lhs rhs t old ar x
  (RuntimeRebase.shared p f lhs rhs t old ar x I) G P Q R hi ha index fuel ⟨hP⟩ ⟨hQ⟩ ⟨hR⟩ ⟨hhi⟩ ⟨hha⟩
 exact ⟨Hilbert.Local.mp (.base (.logical (.andLeft _ _))) h⟩

theorem compose (P Q R hqr hpq index fuel : Term ctx)
 (hP : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval P))
 (hQ : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval Q))
 (hR : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.currentK.fval R))
 (hq : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel
  (iv (RuntimeTags.tags I contra dual) Q R) hqr))
 (hp : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (core I.currentK.coreTag index fuel
  (iv (RuntimeTags.tags I contra dual) P Q) hpq)) :
 let J := RuntimeTags.tags I contra dual
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (iv J P R) (composeValue J P Q R hqr hpq))) :=
 CoreCompose.compose p f lhs rhs t old ar x I G P Q R hqr hpq index fuel hP hQ hR hq hp
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeAlgebra
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeAlgebra
