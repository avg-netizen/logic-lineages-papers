module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.UnaryValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ValiditySupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open OriginalQuantifierLogicalExtension
variable {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx))
theorem negation (a : Term ctx) (arity : Nat)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid arity I.currentK.fval a)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (formulaValid arity I.currentK.fval (FixedFormulaSubstitution.unaryValue I.previous.current.ctag 6 a))) :=
 CurrentQuantifierLogicalCertificate.UnaryValidityProof.unary p _ _ _
  (RuntimeRebase.shared p f lhs rhs t old ar x I).currentK G arity arity 6 a rfl ha

theorem universalNegation (a : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid 1 I.currentK.fval a)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (formulaValid 0 I.currentK.fval (FixedFormulaSubstitution.unaryValue I.previous.current.ctag 10
    (FixedFormulaSubstitution.unaryValue I.previous.current.ctag 6 a)))) := by
 obtain ⟨hn⟩ := negation p f lhs rhs t old ar x I G a 1 ha
 exact CurrentQuantifierLogicalCertificate.UnaryValidityProof.unary p _ _ _
  (RuntimeRebase.shared p f lhs rhs t old ar x I).currentK G 0 1 10 _ rfl hn

theorem existential (a : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid 1 I.currentK.fval a)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (formulaValid 0 I.currentK.fval (FixedFormulaSubstitution.unaryValue I.previous.current.ctag 11 a))) :=
 CurrentQuantifierLogicalCertificate.UnaryValidityProof.unary p _ _ _
  (RuntimeRebase.shared p f lhs rhs t old ar x I).currentK G 0 1 11 a rfl ha

theorem implication (a b : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid 0 I.currentK.fval a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid 0 I.currentK.fval b)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (formulaValid 0 I.currentK.fval (impValue I.previous.current.ctag I.previous.current.atag a b))) :=
 UniformClosedPropositionalCertificate.ImplicationValidityProof.implication p _ _ _ false
  (RuntimeRebase.shared p f lhs rhs t old ar x I).currentK G a b ha hb
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ValiditySupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.ValiditySupport
