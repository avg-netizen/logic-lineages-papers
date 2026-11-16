module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.CodeBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open FixedFormulaSubstitution PrescribedRuntimeCallCongruence
open GorbowPublishedDCB
theorem exactSource : Targets.SourceCore := by
 intro installed lhs rhs k t old a baseX pF pR c hA hn I
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hseed⟩ := CumulativePropositionalSource.SeedProof.seeded installed lhs rhs t old a baseX pF pR c hA hn I
 refine ⟨seedFuel,?_⟩
 intro n kind J target producerTag H ht hp ctx assumptions inputs fuel
 dsimp only
 intro hguard
 let raw := inputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag)
 have hraw : ∀ i, Nonempty (Hilbert.Local U ctx assumptions
  (Continuation20261114.RawReflexivityDispatcher.valid I.previous.previous.current.vtag (raw.get i))) := by
  intro i
  have h := CurrentCompositionCertificate.ValidityProof.previousNumeral p installed lhs rhs t old a
   (SaturatedAxiomLeaf.saturated baseX) I.previous assumptions (inputs.get i)
  have hl := PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut hTU
   (fun psi hmem => ⟨Hilbert.Local.hypothesis hmem⟩) h
  simp only [raw,List.Vector.get_map]
  exact hl
 obtain ⟨hs⟩ := hseed n (rootFormula kind target) (EvaluatorProof.member p kind target ht) ctx assumptions raw fuel hraw hguard
 have hsCore := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hs
 obtain ⟨hf⟩ := RootEncoding.root p installed lhs rhs t old a _ I kind target ht inputs
 obtain ⟨hfU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨hf⟩
 obtain ⟨hfCore⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U assumptions I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hfU) hsCore
 obtain ⟨hc⟩ := CodeBridge.code p installed lhs rhs t old a _ I kind J H target producerTag hp inputs
 obtain ⟨hcU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨Support.equalitySymmetry _ _ hc⟩
 exact CurrentImplicationCertificate.RebaseProof.coreCode U assumptions I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base hcU) hfCore
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SourceProof
