module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.RootEncodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowPublishedDCB PrescribedRuntimeCallCongruence

theorem exactConstructor : Targets.InternalConstructor := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hseed⟩ := CumulativePropositionalSource.SeedProof.seeded
  installed lhs rhs t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro m f g tag hnode ctx G counter inputs previous result childCode fuel
 dsimp only
 intro hguard hchild
 let J := tags I.previous
 let av := CurrentCompositionCertificate.numeralValues J.numeralTag inputs
 let counterRaw := LiteralNumeralPrefix.numeralCall J.numeralTag counter
 let priorNum := LiteralNumeralPrefix.numeralCall J.numeralTag previous
 let priorCall := callValue J (Term.numeral tag) (counterRaw ::ᵥ av)
 let nextCall := callValue J (Term.numeral tag) (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ counter) ::ᵥ av)
 let left := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorCall ::ᵥ av)
 let right := callValue J (Term.numeral (tag+GorbowPRChildTags.stepTag f)) (counterRaw ::ᵥ priorNum ::ᵥ av)
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.previous.current.ctag
  I.previous.previous.current.atag I.previous.previous.current.constructorTag (rootFormula f tag) (counterRaw ::ᵥ av)
 have hraw : ∀ i, Nonempty (Hilbert.Local U ctx G
  (RawReflexivityDispatcher.valid I.previous.previous.current.vtag ((counterRaw ::ᵥ av).get i))) := by
  intro i
  have hval (value : Term ctx) := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU
   (fun psi hmem => ⟨Hilbert.Local.hypothesis hmem⟩)
   (CurrentCompositionCertificate.ValidityProof.previousNumeral p installed lhs rhs t old a
    (SaturatedAxiomLeaf.saturated baseX) I.previous G value)
  cases i using Fin.cases with
  | zero => exact hval counter
  | succ i =>
   simpa only [av,CurrentCompositionCertificate.numeralValues,List.Vector.get_cons_succ,List.Vector.get_map] using hval (inputs.get i)
 obtain ⟨hs⟩ := hseed (m+1) (rootFormula f tag) (SymbolicProof.rootMember p f g tag hnode)
  ctx G (counterRaw ::ᵥ av) fuel hraw hguard
 have hsCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 obtain ⟨he⟩ := RootEncodingProof.root p installed lhs rhs t old a _ I f tag counter av
 obtain ⟨he⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨he⟩
 obtain ⟨hroot⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U G I.currentK.coreTag index fuel
  (PrescribedRuntimeSpecialization.value I.previous.previous.current.ctag I.previous.previous.current.atag (rootFormula f tag) (counterRaw ::ᵥ av))
  (equalValue J.ctag J.atag nextCall left) seed (.base he) hsCore
 let R := core I.currentK.coreTag index fuel (equalValue J.ctag J.atag nextCall left) seed
 let C := core I.currentK.coreTag index fuel (equalValue J.ctag J.atag right output) childCode
 let Gamma := [R,C]
 have hr : Nonempty (Hilbert.Local T ctx Gamma R) := ⟨.hypothesis List.mem_cons_self⟩
 have hc : Nonempty (Hilbert.Local T ctx Gamma C) := ⟨.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have hout := ConstructorCoreProof.assemble p installed lhs rhs t old a _ I f tag Gamma counter inputs previous result childCode index fuel hr hc
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact ⟨hroot⟩
  have he := List.mem_singleton.mp hmem
  subst psi
  exact hchild
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU hG hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.ConstructorProof
