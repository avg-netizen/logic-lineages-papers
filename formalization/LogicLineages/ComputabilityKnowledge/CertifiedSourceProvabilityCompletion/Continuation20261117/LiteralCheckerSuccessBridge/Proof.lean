module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.ExternalProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.GuardProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.LiteralNaturality
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph GorbowSubstitution GorbowFormulaSubstitution
open NaturalityProof SpecializationNaturality LiteralNaturality

theorem exactSource : Targets.Source := by
 intro f lhs rhs old a baseX pF0 pR pCK box c
 dsimp only
 intro hA hbase I carrierTag peelTag baseProducerTag checkerInventoryTag checkerProducerTag hcarrier hpeel hbaseProducer hcheckerInventory hcheckerProducer
 let t := CurrentNamedHeaderCertificate.template
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let K := tags R.previous
 let U := S pF pR q
 obtain ⟨bound,h⟩ := ExternalProof.external f lhs rhs old a baseX pF0 pR pCK box c hA hbase I
  carrierTag peelTag baseProducerTag checkerInventoryTag checkerProducerTag hcarrier hpeel hbaseProducer hcheckerInventory hcheckerProducer
 refine ⟨bound,?_⟩
 intro sigma ctx innerFuel innerCert outerFuel
 let r : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))
 let s : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)
 let literalProof := RetainedBaseLiteralBinary.certificate K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseProducerTag r s
 let checkerProof := CurrentCheckerSuccessCertificate.proofCode checkerProducerTag pF c innerFuel (value pF c sigma) innerCert
 let output := certificate K pF c sigma innerFuel innerCert literalProof checkerProof
 let formula := CurrentPublishedProvabilityIntroduction.checkerEquationCode K pF c sigma innerFuel innerCert
 let premise := CurrentCheckerSuccessCertificate.success pF c innerFuel (value pF c sigma) innerCert
 let gap : Term (ctx+1) := .var 0
 let fuel : Term (ctx+1) := .add (Term.numeral bound) gap
 have hg : Derivation U (orderGuard (Term.numeral bound) fuel) :=
  .mp (FuelWitness.ExtractionLogicProof.orderIntro (Term.numeral bound) fuel gap) (.logical (.reflexive fuel))
 obtain ⟨hgap⟩ := h sigma (ctx+1) (liftTerm innerFuel) (liftTerm innerCert) fuel ⟨hg⟩
 have hnormalized : Nonempty (Derivation U
  (.imp (GorbowPACore.weaken premise)
   (accepted R.currentK.coreTag R.currentK.verifierTag (liftTerm (Term.numeral (n := ctx) (Encodable.encode c))) fuel
    (liftTerm formula) (liftTerm output)))) := by
  simpa only [premise,formula,output,literalProof,checkerProof,r,s,
   GorbowPACore.weaken,CurrentCheckerSuccessCertificate.success,CurrentCheckerSuccessCertificate.checkerInputs,
   CurrentCheckerSuccessCertificate.proofCode,CurrentStructuralProducerCore.code,
   CurrentPublishedProvabilityIntroduction.checkerEquationCode,
   liftTerm,renameTerm,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,
   Logic.substNumeral,substitute,certificateSubst,literalSubst,valueSubst,childCodeSubst,
   PrescribedRuntimeEquality.equalValue,binarySubst,callValueSubst,numeralSubst] using (show Nonempty _ from ⟨hgap⟩)
 exact GuardProof.internalize U bound R.currentK.coreTag R.currentK.verifierTag
  (Term.numeral (Encodable.encode c)) formula output outerFuel premise hnormalized

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Proof
