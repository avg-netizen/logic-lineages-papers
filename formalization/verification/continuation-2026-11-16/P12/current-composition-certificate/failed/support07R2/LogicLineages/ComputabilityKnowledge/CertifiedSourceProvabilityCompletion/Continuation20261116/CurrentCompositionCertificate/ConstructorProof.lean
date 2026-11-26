module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ConstructorCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
theorem exactConstructor : Targets.InternalConstructor := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativeUniformRule12Source.verifier installed lhs rhs old a baseX)
 have hTU := CurrentSourceSeededSpecialization.SourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hseed⟩ := CurrentSourceSeededSpecialization.StatementChecks.exactSeededSpecialization
  installed lhs rhs k t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro m n f g tag hnode ctx G inputs values codes result functionCode fuel
 dsimp only
 intro hguard hchildren hfunction
 let J := tags I
 let av := numeralValues J.numeralTag inputs
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag values
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.current.ctag
  I.previous.current.atag I.previous.current.constructorTag (rootFormula f g tag) av
 let parent := callValue J (Term.numeral tag) av
 let left := callValue J (Term.numeral (tag+1)) bv
 let right := callValue J (Term.numeral (tag+1)) cv
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 have hraw : ∀ i, Nonempty (Hilbert.Local U ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.current.vtag (av.get i))) := by
  intro i
  have h := ValidityProof.previousNumeral p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I G (inputs.get i)
  exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU
   (fun psi hmem => ⟨.hypothesis hmem⟩) h
 obtain ⟨hs⟩ := hseed m (rootFormula f g tag) (RootProof.member p f g tag hnode) ctx G av fuel hraw hguard
 have hsCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 have he := RootEncodingProof.root p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I f g tag av
 obtain ⟨he⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ he
 obtain ⟨hroot⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U G I.current.coreTag index fuel
  (PrescribedRuntimeSpecialization.value I.previous.current.ctag I.previous.current.atag (rootFormula f g tag) av)
  (equalValue J.ctag J.atag parent left) seed (.base he) hsCore
 let P := core I.current.coreTag index fuel (equalValue J.ctag J.atag parent left) seed
 let F := core I.current.coreTag index fuel (equalValue J.ctag J.atag right output) functionCode
 let children := List.ofFn (fun i : Fin n => core I.current.coreTag index fuel
  (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i))
 let Gamma := P :: F :: children
 have hr : Nonempty (Hilbert.Local T ctx Gamma P) := ⟨.hypothesis List.mem_cons_self⟩
 have hf : Nonempty (Hilbert.Local T ctx Gamma F) := ⟨.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have hc : ∀ i, Nonempty (Hilbert.Local T ctx Gamma
  (core I.current.coreTag index fuel (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i))) := by
  intro i
  exact ⟨.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))⟩
 have hout := ConstructorCoreProof.assemble p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
  f g tag Gamma inputs values codes result functionCode index fuel hr hc hf
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact ⟨hroot⟩
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hfunction
  obtain ⟨i,he⟩ := List.mem_ofFn.mp hmem
  subst psi
  exact hchildren i
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU hG hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ConstructorProof
