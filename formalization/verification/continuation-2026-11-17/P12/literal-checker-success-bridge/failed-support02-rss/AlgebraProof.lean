module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
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
 let xs := leftArgs K pF c sigma innerFuel innerCert
 let ys := rightArgs K pF c sigma innerFuel innerCert
 let codes := reflexivityCertificate K (xs.get 0) ::ᵥ reflexivityCertificate K (xs.get 1) ::ᵥ
  reflexivityCertificate K (xs.get 2) ::ᵥ literalProof ::ᵥ reflexivityCertificate K (xs.get 4) ::ᵥ nil
 have hRef (i : Fin 5) : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue K.ctag K.atag (xs.get i) (xs.get i))
   (reflexivityCertificate K (xs.get i)))) := by
  obtain ⟨hi⟩ := hl i
  obtain ⟨h⟩ := CumulativePropositionalSource.NewCallReflexivityProof.current p f lhs rhs t old a x I G
   (xs.get i) index fuel hi
  exact ⟨.mp (.base (.logical (.andLeft _ _))) h⟩
 have hc : ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue K.ctag K.atag (xs.get i) (ys.get i)) (codes.get i))) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact hRef 0
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact hRef 1
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact hRef 2
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact ⟨hLiteral⟩
        · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
          exact hRef 4
 let tag : Term ctx := Term.numeral (GorbowNamedInternalProvability.checkerTag pF)
 obtain ⟨hcalls⟩ := CumulativePropositionalSource.NewCallRuntimeProof.exactTupleAndCall arity k p f lhs rhs t old a x I
  ctx G 5 tag index fuel xs ys codes hl hr hc
 have hCall := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hcalls
 have hCallCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hCall
 have hLeft := CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old a x I.previous G tag xs hl
 have hMid := CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old a x I.previous G tag ys hr
 let H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old a x I
 obtain ⟨hOne⟩ := PrescribedRuntimeCallCongruence.ValidityProof.numeral p old a x I.previous.current K.numeralTag H.hn G (.succ .zero)
 exact CumulativePropositionalSource.NewTransitivityProof.exactTransitivity arity k p f lhs rhs t old a x I
  ctx G _ _ _ _ _ index fuel hLeft hMid ⟨hOne⟩ ⟨hCallCore⟩ ⟨hChecker⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.AlgebraProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.AlgebraProof
