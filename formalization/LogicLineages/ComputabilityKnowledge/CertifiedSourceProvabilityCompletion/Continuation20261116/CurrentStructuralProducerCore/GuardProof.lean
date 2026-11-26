module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.GuardProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem lower (T : Sentence → Prop) {ctx : Nat} (a b d : Nat) (fuel : Term ctx)
 (h : Nonempty (Derivation T (orderGuard (Term.numeral (a+b+d)) fuel))) :
 Nonempty (Derivation T (orderGuard (Term.numeral a) fuel)) ∧
 Nonempty (Derivation T (orderGuard (Term.numeral b) fuel)) ∧
 Nonempty (Derivation T (orderGuard (Term.numeral d) fuel)) := by
 obtain ⟨h⟩ := h
 obtain ⟨ha⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd T a (b+d) fuel
 obtain ⟨hb⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd T b (a+d) fuel
 obtain ⟨hd⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd T d (a+b) fuel
 have ea : a+(b+d)=a+b+d := by omega
 have eb : b+(a+d)=a+b+d := by omega
 have ed : d+(a+b)=a+b+d := by omega
 rw [ea] at ha
 rw [eb] at hb
 rw [ed] at hd
 exact ⟨⟨.mp ha h⟩,⟨.mp hb h⟩,⟨.mp hd h⟩⟩

theorem lift (T : Sentence → Prop) {ctx : Nat} (bound : Nat) (fuel : Term ctx)
 (h : Nonempty (Derivation T (orderGuard (Term.numeral bound) fuel))) :
 Nonempty (Derivation T (orderGuard (Term.numeral bound) (liftTerm fuel))) := by
 obtain ⟨h⟩ := GorbowDerivationSubstitution.Proof.derivationSubstitution T ctx (ctx+1)
  (orderGuard (Term.numeral bound) fuel) (fun i => Term.var i.succ) h
 simp only [FuelWitness.ExtractionLogicProof.substOrder,Logic.substNumeral,liftTerm,GorbowFormulaSubstitution.renameTerm] at h ⊢
 exact ⟨h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.GuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.GuardProof
