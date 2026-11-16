module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CumulativePropositionalSource
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- The complete old published-source contract PLUS actual finite inventory
and anchored installations at ONE selected tuple. Q precedes source selection;
Q is the actual cumulative verifier AST, never the selected root. The new
checker-success bridge is an object-language implication, not an oracle premise. -/
def OneCheckerSource : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k),
 ArithmeticTemplateEvaluation.Arithmetic t →
 let Q : Program 1 → Program 1 → Program 3 → Program 5 :=
  fun old a baseX => CumulativePropositionalSource.verifier f lhs rhs old a baseX
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag btag extraTag inventoryTag evaluatorTag producerTag : Nat),
 ∃ I : JointInstallation
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.currentK.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 I.currentS.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 I.currentK.coreTag = I.currentS.coreTag ∧
 I.currentK.iteratorTag = I.currentS.iteratorTag ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 (nodes (root f lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ ∧
 LiteralValidatedSource.Retained (logical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages f lhs rhs old a baseX offset pF pR c mtag xtag ∧
 CompilerCapability f lhs rhs t old a baseX pF pR I ∧
 EqualityCapability f lhs rhs t old a baseX pF pR I ∧
 FullFormulaCapability f lhs rhs t old a baseX pF pR I ∧
 RetentionCapability f lhs rhs t old a baseX pF pR I ∧
 PriorRetentionCapability f lhs rhs t old a baseX pF pR I ∧
 Uniform13Capability f lhs rhs t old a baseX pF pR I ∧
 Uniform12Capability f lhs rhs t old a baseX pF pR I ∧
 PropositionalCapability f lhs rhs t old a baseX pF pR I ∧
 SeedCapability f lhs rhs t old a baseX pF pR c I ∧
 SpecializationCapability f lhs rhs t old a baseX pF pR c I ∧
 SpecializationTraceCapability f lhs rhs t old a baseX pF pR c I ∧
 CompositionTraceCapability f lhs rhs t old a baseX pF pR c I ∧
 CompositionCapability f lhs rhs t old a baseX pF pR c I ∧
 RecursionBaseTraceCapability f lhs rhs t old a baseX pF pR c I ∧
 RecursionBaseCapability f lhs rhs t old a baseX pF pR c I ∧
 (nodes (root f lhs rhs pF pR old a baseX))[extraTag]? =
  some ⟨6,CurrentStructuralProducerSource.extendedExtra f lhs rhs t Q old a baseX⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[inventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX (Q old a baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[evaluatorTag]? = some ⟨5,Q old a baseX⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨6,CurrentStructuralProducerCompiler.compile (Q old a baseX)⟩ ∧
 (∀ m (u : Program m), Occurs ⟨m,u⟩ (Q old a baseX) → ∀ (target : Nat),
  (nodes (root f lhs rhs pF pR old a baseX))[target]? = some ⟨m,u⟩ →
  ∃ (childProducerTag : Nat),
  (nodes (root f lhs rhs pF pR old a baseX))[childProducerTag]? =
   some ⟨m+1,CurrentStructuralProducerCompiler.compile u⟩ ∧
  CurrentStructuralProducerInventory.InstalledAt (root f lhs rhs pF pR old a baseX)
   f lhs rhs t old a baseX target childProducerTag u) ∧
 (nodes (root f lhs rhs pF pR old a baseX))[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,CumulativePropositionalSource.verifier f lhs rhs old a baseX⟩ ∧
 (∃ outerBound : Nat, ∀ ctx (innerFuel formula certificate : Term ctx),
  Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX))
   (.imp (success pF c innerFuel formula certificate)
    (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c))
     (Term.numeral outerBound) (quotedSuccess (tags I.previous) pF c innerFuel formula certificate)
     (proofCode producerTag pF c innerFuel formula certificate)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Targets
