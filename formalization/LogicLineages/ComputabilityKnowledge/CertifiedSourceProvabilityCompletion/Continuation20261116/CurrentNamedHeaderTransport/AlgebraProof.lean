module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.GraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewUnaryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewTransitivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.AlgebraProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem derive {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old ar x)
 (G : List (Formula ctx)) (aliasTag certTag : Nat) (r s index fuel : Term ctx)
 (halias : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (CurrentNamedAliasCertificate.aliasCode (tags I.previous) r s)
   (call aliasTag (r ::ᵥ s ::ᵥ nil))))
 (hheader : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag
    (CurrentNamedAliasCertificate.headerCode (tags I.previous) r s)
    (LiteralNumeralPrefix.numeralCall (tags I.previous).numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])))
   (call certTag (r ::ᵥ s ::ᵥ nil)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag
    (unaryValue (tags I.previous).ctag 5 (CurrentNamedAliasCertificate.headerCode (tags I.previous) r s))
    (callValue (tags I.previous) (Term.numeral GorbowSourceRegistryPadding.functionTag)
     (LiteralNumeralPrefix.numeralCall (tags I.previous).numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s]) ::ᵥ nil)))
   (GraphProof.result (tags I.previous) aliasTag certTag r s))) := by
 let K := tags I.previous
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old ar x I
 let a := CurrentNamedAliasCertificate.headerCode K r s
 let b := LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])
 obtain ⟨ha⟩ := ValidityProof.headerValid p f lhs rhs t old ar x I G r s
 obtain ⟨hb⟩ := PrescribedRuntimeCallCongruence.ValidityProof.numeral p _ _ _ I.previous.current K.numeralTag H.hn G (GorbowRegistryTuple.headerTerm 2 0 [r,s])
 obtain ⟨hu⟩ := CumulativePropositionalSource.NewUnaryProof.exactUnaryCongruence arity k p f lhs rhs t old ar x I
  1 0 boundEnvironment unary ctx G nil a b (call certTag (r ::ᵥ s ::ᵥ nil)) index fuel
  (fun i => Fin.elim0 i) ⟨ha⟩ ⟨hb⟩ ⟨hheader⟩
 have huc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hu
 obtain ⟨hea⟩ := ValidityProof.unaryEncoding p K H a
 obtain ⟨heb⟩ := ValidityProof.unaryEncoding p K H b
 obtain ⟨hef⟩ := CurrentCompositionCertificate.CodecProof.binary p K.ctag K.atag K.ctag K.atag 0
  H.hc H.ha H.hc H.ha _ _ _ _ hea heb
 obtain ⟨huc'⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula I.currentK.coreTag index fuel _ _ _ (.base hef) huc
 obtain ⟨hl⟩ := ConstructorValidityProof.unary p f lhs rhs t old ar x I.previous G true a ha
 have hmid := CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old ar x I.previous G
  (Term.numeral GorbowSourceRegistryPadding.functionTag) (a ::ᵥ nil) (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact ⟨ha⟩)
 have hright := CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old ar x I.previous G
  (Term.numeral GorbowSourceRegistryPadding.functionTag) (b ::ᵥ nil) (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact ⟨hb⟩)
 exact CumulativePropositionalSource.NewTransitivityProof.exactTransitivity arity k p f lhs rhs t old ar x I
  ctx G _ _ _ _ _ index fuel ⟨hl⟩ hmid hright ⟨halias⟩ ⟨huc'⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.AlgebraProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.AlgebraProof
