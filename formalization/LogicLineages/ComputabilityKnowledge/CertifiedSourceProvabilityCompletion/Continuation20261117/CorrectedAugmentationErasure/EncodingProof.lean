module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.SyntaxProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.EncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution
theorem projection {arity k ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (tag : Nat) (raw : List.Vector (Term ctx) 2) :
 let K := tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag
   (projectionFormula tag) raw)
   (equalValue K.ctag K.atag (callValue K (Term.numeral (tag+1)) raw) (raw.get 0)))) := by
 dsimp only
 let K := tags I.previous
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p installed lhs rhs t old a x I
 let e := PrescribedRuntimeSpecialization.runtimeEnvironment 2
 obtain ⟨hf⟩ := CurrentRecursionProducerCore.FormulaCopy.formula p I.previous.previous.current.ctag I.previous.previous.current.atag
  K.ctag K.atag I.previous.previous.current.h_ctag I.previous.previous.current.h_atag H.hc H.ha raw e (projectionFormula tag)
 obtain ⟨hl⟩ := CurrentCompositionCertificate.CallEncodingProof.call p K H.hc H.ha H.hn e raw (tag+1) (argumentVariables 2)
 rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues] at hl
 have hr : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue K.ctag K.atag e raw (.var 0)) (raw.get 0)) := .logical (.reflexive _)
 obtain ⟨he⟩ := CurrentCompositionCertificate.CodecProof.binary p K.ctag K.atag K.ctag K.atag 0 H.hc H.ha H.hc H.ha
  _ _ _ _ hl hr
 exact ⟨Logic.trans _ _ _ hf he⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.EncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.EncodingProof
