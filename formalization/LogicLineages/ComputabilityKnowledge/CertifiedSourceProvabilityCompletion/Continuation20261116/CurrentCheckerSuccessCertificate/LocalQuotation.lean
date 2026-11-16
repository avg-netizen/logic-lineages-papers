module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.LocalQuotation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem unary {ctx : Nat} (U : Sentence → Prop) (G : List (Formula ctx))
 (tag : Nat) (a b : Term ctx) (h : Hilbert.Local U ctx G (.equal a b)) :
 Nonempty (Hilbert.Local U ctx G (.equal (call tag (a ::ᵥ nil)) (call tag (b ::ᵥ nil)))) := by
 refine ⟨LiteralRawMP.DispatcherSupportProof.callCongruence tag _ _ ?_⟩
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => exact Fin.elim0 i

theorem binaryRight {ctx : Nat} (U : Sentence → Prop) (G : List (Formula ctx))
 (tag : Nat) (left a b : Term ctx) (h : Hilbert.Local U ctx G (.equal a b)) :
 Nonempty (Hilbert.Local U ctx G (.equal (call tag (left ::ᵥ a ::ᵥ nil)) (call tag (left ::ᵥ b ::ᵥ nil)))) := by
 refine ⟨LiteralRawMP.DispatcherSupportProof.callCongruence tag _ _ ?_⟩
 intro i
 cases i using Fin.cases with
 | zero => exact .base (.logical (.reflexive left))
 | succ i => cases i using Fin.cases with
   | zero => exact h
   | succ i => exact Fin.elim0 i

theorem resultOne {ctx : Nat} (U : Sentence → Prop) (J : Tags) (pF : Program 1) (c : Code)
 (innerFuel formula certificate : Term ctx) :
 Nonempty (Hilbert.Local U ctx [success pF c innerFuel formula certificate]
  (.equal
   (CurrentStructuralProducerCore.calculation J (GorbowNamedInternalProvability.checkerTag pF)
    (checkerInputs c innerFuel formula certificate))
   (quotedSuccess J pF c innerFuel formula certificate))) := by
 let args := checkerInputs c innerFuel formula certificate
 let G := [success pF c innerFuel formula certificate]
 have hs : Hilbert.Local U ctx G
  (.equal (call (GorbowNamedInternalProvability.checkerTag pF) args) (.succ .zero)) :=
  .hypothesis (List.mem_cons_self)
 obtain ⟨hn⟩ := unary U G J.numeralTag _ _ hs
 let left := callValue J (Term.numeral (GorbowNamedInternalProvability.checkerTag pF))
  (args.map (LiteralNumeralPrefix.numeralCall J.numeralTag))
 obtain ⟨ha⟩ := binaryRight U G J.atag left _ _ hn
 obtain ⟨hc⟩ := binaryRight U G J.ctag (Term.numeral 0) _ _ ha
 exact ⟨hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.LocalQuotation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.LocalQuotation
