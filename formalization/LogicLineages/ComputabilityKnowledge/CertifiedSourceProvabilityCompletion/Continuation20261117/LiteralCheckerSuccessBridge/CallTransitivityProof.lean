module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.CallTransitivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Generic original call-congruence/transitivity step, independent of any
selected source, box, producer inventory or published literal definitions. -/
theorem derive {arity k ctx n : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (G : List (Formula ctx)) (tag index fuel final checkerProof : Term ctx)
 (xs ys codes : List.Vector (Term ctx) n)
 (hl : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (xs.get i))))
 (hr : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag (ys.get i))))
 (hf : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag final)))
 (hc : ∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue (tags I.previous).ctag (tags I.previous).atag (xs.get i) (ys.get i)) (codes.get i))))
 (hChecker : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag (callValue (tags I.previous) tag ys) final) checkerProof)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag (callValue (tags I.previous) tag xs) final)
   (transitivityCertificate (tags I.previous).mtag (tags I.previous).ctag (tags I.previous).atag (tags I.previous).constructorTag
    (callValue (tags I.previous) tag xs) (callValue (tags I.previous) tag ys) final
    (callCertificate (tags I.previous) tag xs ys codes) checkerProof))) := by
 obtain ⟨hcalls⟩ := CumulativePropositionalSource.NewCallRuntimeProof.exactTupleAndCall arity k p f lhs rhs t old a x I
  ctx G n tag index fuel xs ys codes hl hr hc
 have hCall := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hcalls
 have hCallCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hCall
 have hLeft := CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old a x I.previous G tag xs hl
 have hMid := CurrentCompositionCertificate.ValidityProof.call p f lhs rhs t old a x I.previous G tag ys hr
 exact CumulativePropositionalSource.NewTransitivityProof.exactTransitivity arity k p f lhs rhs t old a x I
  ctx G _ _ _ _ _ index fuel hLeft hMid hf ⟨hCallCore⟩ ⟨hChecker⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.CallTransitivityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.CallTransitivityProof
