module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.FourthCoordinateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.AlgebraProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Only the fourth checker argument changes. The four remaining coordinates
receive actual current-source reflexivity certificates. -/
theorem derive {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (G : List (Formula ctx)) (pF : Program 1) (c : Code) (sigma : Sentence)
 (innerFuel innerCert literalProof checkerProof index fuel : Term ctx)
 (hl : ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((leftArgs (tags I.previous) pF c sigma innerFuel innerCert).get i))))
 (hr : ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((rightArgs (tags I.previous) pF c sigma innerFuel innerCert).get i))))
 (hLiteral : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag
    ((leftArgs (tags I.previous) pF c sigma innerFuel innerCert).get 3)
    ((rightArgs (tags I.previous) pF c sigma innerFuel innerCert).get 3)) literalProof))
 (hChecker : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (CurrentCheckerSuccessCertificate.quotedSuccess (tags I.previous) pF c innerFuel (value pF c sigma) innerCert) checkerProof)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (CurrentPublishedProvabilityIntroduction.checkerEquationCode (tags I.previous) pF c sigma innerFuel innerCert)
   (certificate (tags I.previous) pF c sigma innerFuel innerCert literalProof checkerProof))) := by
 let K := tags I.previous
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old a x I
 obtain ⟨hOne⟩ := PrescribedRuntimeCallCongruence.ValidityProof.numeral p (CumulativeUniformRule12Registry.previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x I.previous.current K.numeralTag H.hn G (.succ .zero)
 exact FourthCoordinateProof.derive p f lhs rhs t old a x I G
  (Term.numeral (GorbowNamedInternalProvability.checkerTag pF)) index fuel
  (LiteralNumeralPrefix.numeralCall K.numeralTag (.succ .zero)) checkerProof
  (LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral (Encodable.encode c)))
  (LiteralNumeralPrefix.numeralCall K.numeralTag innerFuel)
  (LiteralNumeralPrefix.numeralCall K.numeralTag .zero)
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (argument pF c sigma))))
  (LiteralNumeralPrefix.numeralCall K.numeralTag (value pF c sigma))
  (LiteralNumeralPrefix.numeralCall K.numeralTag innerCert) literalProof hl hr ⟨hOne⟩ hLiteral hChecker

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.AlgebraProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.AlgebraProof
