module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.AlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old ar : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX) c)
 (hbase : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX) f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX))
 (J : ArithmeticTemplateEvaluation.TemplateInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX) CurrentNamedHeaderCertificate.template)
 (aliasTag transportTag : Nat)
 (ha : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX))[aliasTag]? = some ⟨2,CurrentNamedAliasCertificate.program⟩)
 (htp : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX))[transportTag]? = some ⟨2,program⟩) :
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ ctx (r s fuel : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX))
  (.imp (orderGuard (Term.numeral bound) fuel)
   (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
    (equalValue (tags R.previous).ctag (tags R.previous).atag
     (unaryValue (tags R.previous).ctag 5 (CurrentNamedAliasCertificate.headerCode (tags R.previous) r s))
     (callValue (tags R.previous) (Term.numeral GorbowSourceRegistryPadding.functionTag)
      (LiteralNumeralPrefix.numeralCall (tags R.previous).numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s]) ::ᵥ nil)))
    (call transportTag (r ::ᵥ s ::ᵥ nil))))) := by
 let p := CumulativePropositionalSource.root f lhs rhs pF pR old ar baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) I
 let U := S pF pR (CumulativePropositionalSource.verifier f lhs rhs old ar baseX)
 let K := tags R.previous
 let incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old ar baseX
 obtain ⟨bound,hAlias⟩ := CurrentNamedAliasCertificate.SourceEndpoint.bridge f lhs rhs t old ar baseX pF pR c hA hbase I aliasTag ha
 refine ⟨bound,?_⟩
 intro ctx r s fuel
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let G := [orderGuard (Term.numeral bound) fuel]
 obtain ⟨haS⟩ := hAlias ctx r s fuel
 have haLocal : Hilbert.Local U ctx G _ := .mp (.base haS) (.hypothesis List.mem_cons_self)
 have haCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) haLocal
 obtain ⟨hhS⟩ := CurrentNamedHeaderCertificate.SourceEndpoint.bridge f lhs rhs t old ar baseX pF pR R J ctx r s index fuel
 have hhCore : Hilbert.Local U ctx G _ := .mp (.base (.logical (.andLeft _ _))) (.base hhS)
 let PA := core R.currentK.coreTag index fuel (CurrentNamedAliasCertificate.aliasCode K r s) (call aliasTag (r ::ᵥ s ::ᵥ nil))
 let PH := core R.currentK.coreTag index fuel
  (equalValue K.ctag K.atag (CurrentNamedAliasCertificate.headerCode K r s)
   (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])))
  (call J.certificateTag (r ::ᵥ s ::ᵥ nil))
 let Gamma := [PA,PH]
 have h := AlgebraProof.derive p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX) R Gamma aliasTag J.certificateTag r s index fuel
  (.hypothesis (by change PA ∈ [PA,PH]; exact List.mem_cons_self))
  (.hypothesis (by change PH ∈ [PA,PH]; exact List.mem_cons_of_mem PA List.mem_cons_self))
 have hg : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hm
  simp only [Gamma,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with he | he
  · subst psi; exact ⟨haCore⟩
  · subst psi; exact ⟨hhCore⟩
 obtain ⟨hresult⟩ := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl hg h
 have hc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hresult
 have HI : CurrentCallCongruenceProgram.Installation p K :=
  ⟨R.previous.current.h_ctag,R.previous.current.h_atag,R.previous.previous.previous.previous.previous.hnumeral,
   R.previous.previous.previous.previous.previous.hmp,R.previous.current.h_constructor,
   R.previous.previous.previous.previous.previous.hc,R.previous.previous.previous.previous.previous.hreflexivity⟩
 obtain ⟨he⟩ := GraphProof.graph p K HI aliasTag J.certificateTag ha J.hcertificate r s transportTag htp
 obtain ⟨heS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨he⟩
 obtain ⟨hc'⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U G R.currentK.coreTag index fuel _ _ _
  (.base (Support.equalitySymmetry _ _ heS)) hc
 obtain ⟨hout⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p f lhs rhs t old ar
  (SaturatedAxiomLeaf.saturated baseX) R U incl G _ _ index fuel hc'
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.SourceEndpoint
