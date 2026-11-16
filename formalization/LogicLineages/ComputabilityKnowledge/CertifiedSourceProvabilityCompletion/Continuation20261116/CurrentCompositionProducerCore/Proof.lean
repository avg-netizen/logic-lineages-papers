module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CodeBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem exactSource : Targets.SourceCore := by
 intro installed lhs rhs k t old a baseX pF pR c hA hbase I
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 have hTU := CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX
 obtain ⟨seedFuel,hconstructor⟩ := CumulativePropositionalSource.NewCompositionConstructorProof.exactConstructor
  installed lhs rhs t old a baseX pF pR c hA hbase I
 refine ⟨seedFuel,?_⟩
 intro m n f g F G J target producerTag H hroot hproducer ctx assumptions inputs fuel
 dsimp only
 intro hguard hchildren hfunction
 let K := tags I.previous
 let values := childValues f g target inputs
 let result := call (target+1) values
 let codes := List.Vector.ofFn (fun i => producerCode (J.argumentProducerTags i) (target+argumentTag f g i) inputs)
 let functionCode := producerCode J.functionProducerTag (target+1) values
 let index : Term ctx := Term.numeral (Encodable.encode c)
 have hchildren' : ∀ i, Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel
   (equalValue K.ctag K.atag
    ((CurrentCompositionCertificate.childValues K f g target (CurrentCompositionCertificate.numeralValues K.numeralTag inputs)).get i)
    ((CurrentCompositionCertificate.numeralValues K.numeralTag values).get i)) (codes.get i))) := by
  intro i
  simp only [CurrentCompositionCertificate.childValues,CurrentCompositionCertificate.numeralValues,
   List.Vector.get_ofFn,List.Vector.get_map,codes,values,childValues]
  exact hchildren i
 have hfunction' : Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel
   (equalValue K.ctag K.atag
    (callValue K (Term.numeral (target+1)) (CurrentCompositionCertificate.numeralValues K.numeralTag values))
    (LiteralNumeralPrefix.numeralCall K.numeralTag result)) functionCode)) := by
  exact hfunction
 obtain ⟨haccepted⟩ := hconstructor m n f g target hroot ctx assumptions inputs values codes result functionCode fuel hguard hchildren' hfunction'
 have hc := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) haccepted
 obtain ⟨heval⟩ := EvaluationBridge.root p f g target hroot inputs
 obtain ⟨hformula⟩ := CurrentRecursionProducerCore.FormulaBridge.changeResult p K target inputs result heval
 obtain ⟨hformulaU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hformula⟩
 obtain ⟨hcFormula⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U assumptions I.currentK.coreTag index fuel
  _ _ _ (.base hformulaU) hc
 obtain ⟨hcode⟩ := CodeBridge.actual p installed lhs rhs t old a baseX I f g F G J H target producerTag hroot hproducer inputs
 obtain ⟨hcodeU⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨NamedArithmeticGraph.Support.equalitySymmetry _ _ hcode⟩
 obtain ⟨hcCode⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U assumptions I.currentK.coreTag index fuel
  _ _ _ (.base hcodeU) hcFormula
 exact CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p installed lhs rhs t old a _ I U hTU assumptions
  _ _ index fuel hcCode

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Proof
