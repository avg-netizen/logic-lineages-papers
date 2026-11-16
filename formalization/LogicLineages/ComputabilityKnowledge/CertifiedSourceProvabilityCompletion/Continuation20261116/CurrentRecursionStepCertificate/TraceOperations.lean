module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TracePrimitives
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceOperations
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem singleton {arity ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma) (ctag tag : Nat) (isS : Bool)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨3,UniformClosedPropositional.lineConstructor isS⟩)
 (a b c : Term ctx) (A B C : Formula 0)
 (ha : Derivation T (.equal a (formulaNumeral A)))
 (hb : Derivation T (.equal b (formulaNumeral B)))
 (hcF : Derivation T (.equal c (formulaNumeral C))) :
 Nonempty (Derivation T
  (.equal (UniformClosedPropositionalCertificate.certificate ctag tag a b c)
   (Term.numeral (UniformClosedPropositional.singletonNumber isS A B C)))) := by
 have hl := Logic.callCongruence T tag
  (a ::ᵥ b ::ᵥ c ::ᵥ nil) (formulaNumeral A ::ᵥ formulaNumeral B ::ᵥ formulaNumeral C ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact ha
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => cases i using Fin.cases with
       | zero => exact hcF
       | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := SingletonTraceProof.singleton p ctag tag isS hc ht A B C (ctx := ctx)
 obtain ⟨hn⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hn⟩
 exact ⟨Logic.trans _ _ _ hs hn⟩
theorem lift {arity k ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x) (aF bF code : Term ctx) (A B : Formula 0) (h : Nat)
 (ha : Derivation T (.equal aF (formulaNumeral A)))
 (hb : Derivation T (.equal bF (formulaNumeral B)))
 (hh : Derivation T (.equal code (Term.numeral h))) :
 Nonempty (Derivation T
  (.equal (liftCertificate I aF bF code) (Term.numeral (liftNumber A B h)))) := by
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 obtain ⟨hk⟩ := singleton p T hT I.currentK.ctag I.currentK.constructorTag false I.currentK.h_ctag I.currentK.h_constructorTag
  aF bF aF A B A ha hb ha
 obtain ⟨hf⟩ := TracePrimitives.imp p T hT J.ctag J.atag I.previous.current.h_ctag I.previous.current.h_atag
  bF aF B A hb ha
 exact TracePrimitives.mp p T hT J.mtag I.previous.previous.previous.previous.previous.hmp
  (impValue J.ctag J.atag bF aF) _ code (.imp B A) _ h hf hk hh
theorem mpUnder {arity k ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x) (pF qF rF hi ha : Term ctx) (P Q R : Formula 0) (i aN : Nat)
 (hp : Derivation T (.equal pF (formulaNumeral P)))
 (hq : Derivation T (.equal qF (formulaNumeral Q)))
 (hr : Derivation T (.equal rF (formulaNumeral R)))
 (hiN : Derivation T (.equal hi (Term.numeral i)))
 (haN : Derivation T (.equal ha (Term.numeral aN))) :
 Nonempty (Derivation T
  (.equal (mpUnderCertificate I pF qF rF hi ha) (Term.numeral (mpUnderNumber P Q R i aN)))) := by
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 have hc := I.previous.current.h_ctag
 have hap := I.previous.current.h_atag
 have hm := I.previous.previous.previous.previous.previous.hmp
 obtain ⟨hs⟩ := singleton p T hT I.currentS.ctag I.currentS.constructorTag true I.currentS.h_ctag I.currentS.h_constructorTag
  pF qF rF P Q R hp hq hr
 obtain ⟨hpq⟩ := TracePrimitives.imp p T hT J.ctag J.atag hc hap pF qF P Q hp hq
 obtain ⟨hpr⟩ := TracePrimitives.imp p T hT J.ctag J.atag hc hap pF rF P R hp hr
 obtain ⟨hmid⟩ := TracePrimitives.imp p T hT J.ctag J.atag hc hap
  (impValue J.ctag J.atag pF qF) (impValue J.ctag J.atag pF rF) (.imp P Q) (.imp P R) hpq hpr
 obtain ⟨hfirst⟩ := TracePrimitives.mp p T hT J.mtag hm
  (impValue J.ctag J.atag (impValue J.ctag J.atag pF qF) (impValue J.ctag J.atag pF rF))
  _ hi (.imp (.imp P Q) (.imp P R)) _ i hmid hs hiN
 exact TracePrimitives.mp p T hT J.mtag hm
  (impValue J.ctag J.atag pF rF) _ ha (.imp P R) _ aN hpr hfirst haN
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceOperations
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TraceOperations
