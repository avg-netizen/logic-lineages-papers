module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TermSubstitution
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.BodyCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution

theorem body {arity d e r s ctx : Nat} (p : Program arity) (c a : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (left : Environment 5 d r) (right : Environment 5 e s) (xs : List.Vector (Term ctx) r) (ys : List.Vector (Term ctx) s)
 (hvars : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue c a left xs (.var i)) (termValue c a right ys (.var i))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue c a xs bodyTemplate left) (formulaValue c a ys bodyTemplate right))) := by
 have ht := CurrentRecursionProducerCore.TermSubstitution.congruence p c a hc ha left right xs ys hvars
 obtain ⟨hl⟩ := ht (CurrentRecursionBaseProgram.openCall (.var 4)
  (.var 2 ::ᵥ .var 1 ::ᵥ .zero ::ᵥ .var 3 ::ᵥ .var 0 ::ᵥ nil))
 obtain ⟨hr⟩ := ht (.succ .zero)
 exact CurrentCompositionCertificate.CodecProof.binary p c a c a 0 hc ha hc ha _ _ _ _ hl hr

theorem outerSpecialization {arity ctx : Nat} (p : Program arity) (J : GraphInterface.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (ntag : Nat) (v : List.Vector (Term ctx) 7) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue J.ctag J.atag
    (GraphInterface.numeral ntag (v.get 2) ::ᵥ GraphInterface.outerInputs ntag v) (.ex bodyTemplate)
    (UniformRuntimeEnvironmentAgreement.specialize outerEnvironment))
   (unaryValue J.ctag 11 (GraphInterface.innerValue J ntag v)))) := by
 obtain ⟨hb⟩ := body p J.ctag J.atag hc ha
  (liftEnvironment (UniformRuntimeEnvironmentAgreement.specialize outerEnvironment)) innerEnvironment
  (GraphInterface.numeral ntag (v.get 2) ::ᵥ GraphInterface.outerInputs ntag v) (GraphInterface.innerInputs ntag v) (fun i => by
   cases i using Fin.cases with
   | zero => exact ⟨.logical (.reflexive _)⟩
   | succ i => cases i using Fin.cases with
    | zero => exact ⟨.logical (.reflexive _)⟩
    | succ i => cases i using Fin.cases with
     | zero => exact ⟨.logical (.reflexive _)⟩
     | succ i => cases i using Fin.cases with
      | zero => exact ⟨.logical (.reflexive _)⟩
      | succ i => cases i using Fin.cases with
       | zero => exact ⟨.logical (.reflexive _)⟩
       | succ i => exact Fin.elim0 i)
 exact CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 11 hc hc _ _ hb
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.BodyCongruence
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.BodyCongruence
