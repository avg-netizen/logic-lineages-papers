module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.QuoteProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.Retarget
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CompilerCapabilityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX) f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX))
 (J : ArithmeticTemplateEvaluation.TemplateInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX) template) :
 ∀ ctx (r s index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (equalValue (tags I.previous).ctag (tags I.previous).atag
    (CurrentNamedAliasCertificate.headerCode (tags I.previous) r s)
    (LiteralNumeralPrefix.numeralCall (tags I.previous).numeralTag
     (GorbowRegistryTuple.headerTerm 2 0 [r,s])))
   (call J.certificateTag (r ::ᵥ s ::ᵥ nil)))) := by
 intro ctx r s index fuel
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let U := S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX)
 let K := tags I.previous
 let A := I.previous.previous.previous.previous.previous.toArithmetic
 let R := Retarget.installation I J
 let incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX
 have H := CurrentRecursionProducerCore.FormulaBridge.originalNodes p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 obtain ⟨he⟩ := CumulativePropositionalSource.CompilerCapabilityProof.compiler f lhs rhs template
  TemplateProof.arithmetic old ar baseX pF pR R ctx (r ::ᵥ s ::ᵥ nil) index fuel
 have hc := Derivation.mp (.logical (.andRight _ _)) he
 obtain ⟨hq⟩ := QuoteProof.quote p old ar (SaturatedAxiomLeaf.saturated baseX) A J K H rfl r s
 obtain ⟨hf⟩ := CurrentCompositionCertificate.CodecProof.binary p A.consTag A.appendTag K.ctag K.atag 0
  A.hc A.ha H.hc H.ha _ _ _ _ hq (.logical (.reflexive _))
 rw [TemplateProof.value] at hc
 obtain ⟨hfS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨hf⟩
 obtain ⟨hcore⟩ := PrescribedRuntimeEquality.LogicProof.coreFormula I.currentK.coreTag index fuel
  _ _ _ (Hilbert.Local.base (Gamma := []) hfS) (.base hc)
 obtain ⟨hout⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old ar
  (SaturatedAxiomLeaf.saturated baseX) I U incl [] _ _ index fuel hcore
 exact ⟨hout.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.SourceEndpoint
