module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionInterface
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CompositionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem composition (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (lb cb rb : Nat)
 (hC : BoundInterfaces.Composition installed lhs rhs t old a baseX pF pR c I cb)
 {n m j : Nat} (q : Program n) (inventoryTag : Nat)
 (hInventory : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[inventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier installed lhs rhs t old a baseX q⟩)
 (f : Program j) (g : Fin j → Program m) (hu : Occurs ⟨m,.composition f g⟩ q)
 (hf : InductionInterface.Correct installed lhs rhs t old a baseX pF pR c I (lb+cb+rb) f)
 (hg : ∀ i, InductionInterface.Correct installed lhs rhs t old a baseX pF pR c I (lb+cb+rb) (g i)) :
 InductionInterface.Correct installed lhs rhs t old a baseX pF pR c I (lb+cb+rb) (.composition f g) := by
 intro target producerTag hq hp ctx inputs fuel
 dsimp only
 intro hguard
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 obtain ⟨J,hJ,hJf,hJg⟩ := CurrentStructuralProducerInventory.CompositionProof.installed p installed lhs rhs t old a baseX I
  q inventoryTag hInventory f g hu target producerTag hq
 obtain ⟨hcGuard⟩ := (GuardProof.lower U lb cb rb fuel hguard).2.1
 let values := CurrentCompositionProducerCore.childValues f g target inputs
 have hargs : ∀ i, Nonempty (Hilbert.Local U ctx []
  (core I.currentK.coreTag (Term.numeral (Encodable.encode c)) fuel
   (calculation (tags I.previous) (target+argumentTag f g i) inputs)
   (code (J.argumentProducerTags i) (target+argumentTag f g i) inputs))) := by
  intro i
  have hi := hg i (target+argumentTag f g i) (J.argumentProducerTags i)
   (Equations.argumentChild p target f g hq i) (hJ.hG i) ctx inputs fuel hguard
  obtain ⟨hi⟩ := CoreTools.project U _ _ _ _ _ _ hi
  exact ⟨.base hi⟩
 have hfun := hf (target+1) J.functionProducerTag (Equations.functionChild p target f g hq)
  hJ.hF ctx values fuel hguard
 obtain ⟨hfun⟩ := CoreTools.project U _ _ _ _ _ _ hfun
 obtain ⟨hout⟩ := hC m j f g (CurrentStructuralProducerCompiler.compile f)
  (fun i => CurrentStructuralProducerCompiler.compile (g i)) J target producerTag hJ hq hp
  ctx [] inputs fuel ⟨.base hcGuard⟩ hargs ⟨.base hfun⟩
 exact ⟨Hilbert.Local.finish hout⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CompositionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CompositionProof
