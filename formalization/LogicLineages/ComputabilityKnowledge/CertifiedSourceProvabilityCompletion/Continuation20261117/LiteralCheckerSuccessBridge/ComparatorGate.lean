module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Expanded original five-input checker equation and explicit congruence/transitivity recipe. -/
theorem originalContract : Targets.Source ↔ (
∀ (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (box : Program 6) (c : Code),
 let t := CurrentNamedHeaderCertificate.template
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 Actual pF pR q c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ (carrierTag peelTag baseProducerTag checkerInventoryTag checkerProducerTag : Nat),
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ →
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ →
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ →
 (nodes root)[checkerInventoryTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX q⟩ →
 (nodes root)[checkerProducerTag]? = some ⟨6,CurrentStructuralProducerCompiler.compile q⟩ →
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ (sigma : Sentence) ctx (innerFuel innerCert outerFuel : Term ctx),
 let K := tags R.previous
 let r : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))
 let s : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)
 let literalProof := RetainedBaseLiteralBinary.certificate K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseProducerTag r s
 let numericalArgument : Term ctx := GorbowBooleanTruth.binaryCodeTerm 0 r s
 let xs := LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral (Encodable.encode c)) ::ᵥ
  LiteralNumeralPrefix.numeralCall K.numeralTag innerFuel ::ᵥ
  LiteralNumeralPrefix.numeralCall K.numeralTag .zero ::ᵥ
  Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode
   (GorbowBooleanTruth.binaryCodeTerm (n := 0) 0
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))))) ::ᵥ
  LiteralNumeralPrefix.numeralCall K.numeralTag innerCert ::ᵥ nil
 let numericalInputs := Term.numeral (Encodable.encode c) ::ᵥ innerFuel ::ᵥ .zero ::ᵥ numericalArgument ::ᵥ innerCert ::ᵥ nil
 let ys := numericalInputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag)
 let coordinateCodes := reflexivityCertificate K (xs.get 0) ::ᵥ reflexivityCertificate K (xs.get 1) ::ᵥ
  reflexivityCertificate K (xs.get 2) ::ᵥ literalProof ::ᵥ reflexivityCertificate K (xs.get 4) ::ᵥ nil
 let checkerTag : Term ctx := Term.numeral (GorbowNamedInternalProvability.checkerTag pF)
 let one := LiteralNumeralPrefix.numeralCall K.numeralTag (.succ .zero)
 let checkerProof := CurrentStructuralProducerCore.code checkerProducerTag
  (GorbowNamedInternalProvability.checkerTag pF) numericalInputs
 Nonempty (Derivation (S pF pR q)
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral bound) outerFuel)
   (.imp (.equal (call (GorbowNamedInternalProvability.checkerTag pF) numericalInputs) (.succ .zero))
    (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) outerFuel
     (equalValue K.ctag K.atag (callValue K checkerTag xs) one)
     (transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
      (callValue K checkerTag xs) (callValue K checkerTag ys) one
      (callCertificate K checkerTag xs ys coordinateCodes) checkerProof)))))
 ) := Iff.rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ComparatorGate
