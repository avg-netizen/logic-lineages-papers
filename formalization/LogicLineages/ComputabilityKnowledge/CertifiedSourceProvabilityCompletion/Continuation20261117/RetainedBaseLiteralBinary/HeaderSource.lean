module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.AliasProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.HeaderAlgebra
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.HeaderSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution

def code {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags) (rule13Tag headerTag : Nat) (r s : Term ctx) : Term ctx :=
 let h := CurrentNamedAliasCertificate.headerCode K r s
 let v := LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (unaryValue K.ctag 5 h) (callValue K (Term.numeral 6) (h ::ᵥ nil)) (callValue K (Term.numeral 6) (v ::ᵥ nil))
  (aliasCertificate K rule13Tag r s)
  (PrescribedRuntimeCallCongruence.unaryCertificate K CurrentNamedHeaderTransport.unary h v (call headerTag (r ::ᵥ s ::ᵥ nil)))

theorem bridge {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (J : ArithmeticTemplateEvaluation.TemplateInstallation
  (CumulativePropositionalSource.root f lhs rhs pF pR old a baseX) CurrentNamedHeaderCertificate.template) :
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ ctx (r s fuel : Term ctx),
 let K := tags R.previous
 let U := S pF pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX)
 Nonempty (Derivation U (orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
  (equalValue K.ctag K.atag (unaryValue K.ctag 5 (CurrentNamedAliasCertificate.headerCode K r s))
   (RetainedBaseSourceCalculation.rawCall K 6 (GorbowRegistryTuple.headerTerm 2 0 [r,s])))
  (code K R.previous.previous.current.constructorTag J.certificateTag r s))) := by
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let U := S pF pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX)
 let K := tags R.previous
 have incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old a baseX
 obtain ⟨bound,ha⟩ := AliasProof.bridge f lhs rhs t old a baseX pF pR c hA hn I
 refine ⟨bound,?_⟩
 intro ctx r s fuel
 dsimp only
 intro hg
 obtain ⟨hg⟩ := hg
 obtain ⟨ha⟩ := ha ctx r s fuel
 have ha := Derivation.mp ha hg
 obtain ⟨hh⟩ := CurrentNamedHeaderCertificate.SourceEndpoint.bridge f lhs rhs t old a baseX pF pR R J ctx r s (Term.numeral (Encodable.encode c)) fuel
 have hac := Derivation.mp (.logical (.andLeft _ _)) ha
 have hhc := Derivation.mp (.logical (.andLeft _ _)) hh
 let A := core R.currentK.coreTag (Term.numeral (Encodable.encode c)) fuel (CurrentNamedAliasCertificate.aliasCode K r s)
  (aliasCertificate K R.previous.previous.current.constructorTag r s)
 let B := core R.currentK.coreTag (Term.numeral (Encodable.encode c)) fuel
  (equalValue K.ctag K.atag (CurrentNamedAliasCertificate.headerCode K r s)
   (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])))
  (call J.certificateTag (r ::ᵥ s ::ᵥ nil))
 let G := [A,B]
 have h := HeaderAlgebra.derive root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R G J.certificateTag r s
  (Term.numeral (Encodable.encode c)) fuel (aliasCertificate K R.previous.previous.current.constructorTag r s)
  (.hypothesis (by change A ∈ [A,B]; exact List.mem_cons_self))
  (.hypothesis (by change B ∈ [A,B]; exact List.mem_cons_of_mem A List.mem_cons_self))
 have hhyp : ∀ phi, phi ∈ G → Nonempty (Hilbert.Local U ctx [] phi) := by
  intro phi hm
  simp only [G,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with he | he
  · subst phi; exact ⟨.base hac⟩
  · subst phi; exact ⟨.base hhc⟩
 obtain ⟨hout⟩ := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut incl hhyp h
 exact ⟨hout.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.HeaderSource
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.HeaderSource
