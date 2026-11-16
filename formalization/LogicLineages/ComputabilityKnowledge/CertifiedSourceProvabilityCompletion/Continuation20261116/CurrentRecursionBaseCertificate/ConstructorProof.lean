module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.ConstructorCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality FixedFormulaSubstitution
open GorbowPublishedDCB
theorem exactConstructor : Targets.InternalConstructor := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)
 have hTU := CurrentSourceSeededSpecialization.SourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hseed⟩ := CurrentSourceSeededSpecialization.StatementChecks.exactSeededSpecialization
  installed lhs rhs k t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro m f g tag hnode ctx G inputs result childCode fuel
 dsimp only
 intro hguard hchild
 let J := tags I
 let av := numeralValues J.numeralTag inputs
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.current.ctag
  I.previous.current.atag I.previous.current.constructorTag (rootFormula m tag) av
 let parent := callValue J (Term.numeral tag) (zero ::ᵥ av)
 let child := callValue J (Term.numeral (tag+1)) av
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 have hraw : ∀ i, Nonempty (Hilbert.Local U ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag (av.get i))) := by
  intro i
  have h := CurrentCompositionCertificate.ValidityProof.previousNumeral p installed lhs rhs t old a
   (SaturatedAxiomLeaf.saturated baseX) I G (inputs.get i)
  simpa only [av,numeralValues,CurrentCompositionCertificate.numeralValues,List.Vector.get_map] using
   (PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU
    (fun psi hmem => ⟨.hypothesis hmem⟩) h)
 obtain ⟨hs⟩ := hseed m (rootFormula m tag) (RootProof.member p f g tag hnode) ctx G av fuel hraw hguard
 have hsCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 have he := RootEncodingProof.root p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I tag av
 obtain ⟨he⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ he
 obtain ⟨hroot⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U G I.current.coreTag index fuel
  (PrescribedRuntimeSpecialization.value I.previous.current.ctag I.previous.current.atag (rootFormula m tag) av)
  (equalValue J.ctag J.atag parent child) seed (.base he) hsCore
 let P := core I.current.coreTag index fuel (equalValue J.ctag J.atag parent child) seed
 let F := core I.current.coreTag index fuel (equalValue J.ctag J.atag child output) childCode
 let Gamma := [P,F]
 have hr : Nonempty (Hilbert.Local T ctx Gamma P) := ⟨.hypothesis List.mem_cons_self⟩
 have hf : Nonempty (Hilbert.Local T ctx Gamma F) := ⟨.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have hout := ConstructorCoreProof.assemble p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
  tag Gamma inputs result childCode index fuel hr hf
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact ⟨hroot⟩
  have he := List.mem_singleton.mp hmem
  subst psi
  exact hchild
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU hG hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.ConstructorProof
