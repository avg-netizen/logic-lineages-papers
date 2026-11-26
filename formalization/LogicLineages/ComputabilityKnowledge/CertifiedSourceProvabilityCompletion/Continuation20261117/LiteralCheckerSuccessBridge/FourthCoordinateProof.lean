module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.CallTransitivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.FourthCoordinateProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Generic five-coordinate proof, all source-dependent terms are opaque scalar
parameters. Only coordinate three changes; other evidence is constructed here. -/
theorem derive {arity k ctx : Nat} (p : Program arity) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (G : List (Formula ctx)) (tag index fuel final checkerProof : Term ctx)
 (a0 a1 a2 left right a4 literalProof : Term ctx)
 (hl : ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ left ::ᵥ a4 ::ᵥ nil).get i))))
 (hr : ∀ i : Fin 5, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag ((a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ right ::ᵥ a4 ::ᵥ nil).get i))))
 (hf : Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.previous.current.vtag final)))
 (hLiteral : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue (tags I.previous).ctag (tags I.previous).atag left right) literalProof))
 (hChecker : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel (equalValue (tags I.previous).ctag (tags I.previous).atag
   (callValue (tags I.previous) tag (a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ right ::ᵥ a4 ::ᵥ nil)) final) checkerProof)) :
 let K := tags I.previous
 let xs := a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ left ::ᵥ a4 ::ᵥ nil
 let ys := a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ right ::ᵥ a4 ::ᵥ nil
 let codes := reflexivityCertificate K a0 ::ᵥ reflexivityCertificate K a1 ::ᵥ reflexivityCertificate K a2 ::ᵥ literalProof ::ᵥ reflexivityCertificate K a4 ::ᵥ nil
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue K.ctag K.atag (callValue K tag xs) final)
   (transitivityCertificate K.mtag K.ctag K.atag K.constructorTag (callValue K tag xs) (callValue K tag ys) final
    (callCertificate K tag xs ys codes) checkerProof))) := by
 let K := tags I.previous
 let xs := a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ left ::ᵥ a4 ::ᵥ nil
 let ys := a0 ::ᵥ a1 ::ᵥ a2 ::ᵥ right ::ᵥ a4 ::ᵥ nil
 let codes := reflexivityCertificate K a0 ::ᵥ reflexivityCertificate K a1 ::ᵥ reflexivityCertificate K a2 ::ᵥ literalProof ::ᵥ reflexivityCertificate K a4 ::ᵥ nil
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
 exact CallTransitivityProof.derive p f lhs rhs t old a x I G tag index fuel final checkerProof xs ys codes hl hr hf hc hChecker

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.FourthCoordinateProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.FourthCoordinateProof
