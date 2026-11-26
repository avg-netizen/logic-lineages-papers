module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.ConstructorCoreProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCallRuntimeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentCompositionCertificate
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
theorem exactConstructor {k : Nat} (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (verifier installed lhs rhs old a baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : JointInstallation (root installed lhs rhs pF pR old a baseX) installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 CompositionCapability installed lhs rhs t old a baseX pF pR c I := by
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hseed⟩ := SeedProof.seeded
  installed lhs rhs t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro m n f g tag hnode ctx G inputs values codes result functionCode fuel
 dsimp only
 intro hguard hchildren hfunction
 let J := tags I.previous
 let av := numeralValues J.numeralTag inputs
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag values
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.previous.current.ctag
  I.previous.previous.current.atag I.previous.previous.current.constructorTag (rootFormula f g tag) av
 let parent := callValue J (Term.numeral tag) av
 let left := callValue J (Term.numeral (tag+1)) bv
 let right := callValue J (Term.numeral (tag+1)) cv
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 have hraw : ∀ i, Nonempty (Hilbert.Local U ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.previous.current.vtag (av.get i))) := by
  intro i
  have h := CurrentCompositionCertificate.ValidityProof.previousNumeral p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I.previous G (inputs.get i)
  simpa only [av,numeralValues,List.Vector.get_map] using
   (PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU
    (fun psi hmem => ⟨.hypothesis hmem⟩) h)
 obtain ⟨hs⟩ := hseed m (rootFormula f g tag) (CurrentCompositionCertificate.RootProof.member p f g tag hnode) ctx G av fuel hraw hguard
 have hsCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 have he := CurrentCompositionCertificate.RootEncodingProof.root p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I.previous f g tag av
 obtain ⟨he⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ he
 obtain ⟨hroot⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U G I.currentK.coreTag index fuel
  (PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag (rootFormula f g tag) av)
  (equalValue J.ctag J.atag parent left) seed (.base he) hsCore
 let P := core I.currentK.coreTag index fuel (equalValue J.ctag J.atag parent left) seed
 let F := core I.currentK.coreTag index fuel (equalValue J.ctag J.atag right output) functionCode
 let children := List.ofFn (fun i : Fin n => core I.currentK.coreTag index fuel
  (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i))
 let Gamma := P :: F :: children
 have hr : Nonempty (Hilbert.Local T ctx Gamma P) := ⟨.hypothesis List.mem_cons_self⟩
 have hf : Nonempty (Hilbert.Local T ctx Gamma F) := ⟨.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have hc : ∀ i, Nonempty (Hilbert.Local T ctx Gamma
  (core I.currentK.coreTag index fuel (equalValue J.ctag J.atag (bv.get i) (cv.get i)) (codes.get i))) := by
  intro i
  exact ⟨.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))⟩
 have hout := NewCompositionConstructorCoreProof.assemble p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorProof
