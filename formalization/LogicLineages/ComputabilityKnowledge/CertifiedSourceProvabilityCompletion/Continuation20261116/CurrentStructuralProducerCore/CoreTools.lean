module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CoreTools
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem project {ctx : Nat} (U : Sentence → Prop) (coreTag verifierTag : Nat)
 (index fuel formula cert : Term ctx)
 (h : Nonempty (Derivation U (accepted coreTag verifierTag index fuel formula cert))) :
 Nonempty (Derivation U (core coreTag index fuel formula cert)) := by
 obtain ⟨h⟩ := h
 exact ⟨.mp (.logical (.andLeft _ _)) h⟩

theorem ofCore {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (U : Sentence → Prop) (hTU : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → U sigma)
 (index fuel formula cert : Term ctx)
 (h : Nonempty (Derivation U (core I.currentK.coreTag index fuel formula cert))) :
 Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel formula cert)) := by
 obtain ⟨h⟩ := h
 obtain ⟨ha⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old a x I U hTU []
  formula cert index fuel (.base h)
 exact ⟨Hilbert.Local.finish ha⟩

theorem transport {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (U : Sentence → Prop) (hTU : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → U sigma)
 (index fuel phi psi cert cert' : Term ctx)
 (hf : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal phi psi)))
 (hc : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal cert cert')))
 (h : Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel phi cert))) :
 Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel psi cert')) := by
 obtain ⟨hf⟩ := GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hf
 obtain ⟨hc⟩ := GorbowTheoryProofProof.monotonicity _ U hTU ctx _ hc
 obtain ⟨h⟩ := project U _ _ index fuel phi cert h
 obtain ⟨hfcore⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [] I.currentK.coreTag
  index fuel phi psi cert (.base hf) (.base h)
 obtain ⟨hccore⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U [] I.currentK.coreTag
  index fuel psi cert cert' (.base hc) hfcore
 exact ofCore p f lhs rhs t old a x I U hTU index fuel psi cert' ⟨Hilbert.Local.finish hccore⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CoreTools
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CoreTools
