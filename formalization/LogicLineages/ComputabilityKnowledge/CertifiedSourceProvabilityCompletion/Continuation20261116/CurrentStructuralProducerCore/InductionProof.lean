module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.LeafProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CompositionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem engine (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (lb cb rb : Nat)
 (hL : BoundInterfaces.Leaf installed lhs rhs t old a baseX pF pR c I lb)
 (hC : BoundInterfaces.Composition installed lhs rhs t old a baseX pF pR c I cb)
 (hR : BoundInterfaces.Recursion installed lhs rhs t old a baseX pF pR c I rb)
 {n : Nat} (q : Program n) (inventoryTag : Nat)
 (hInventory : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[inventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier installed lhs rhs t old a baseX q⟩) :
 ∀ m (u : Program m), Occurs ⟨m,u⟩ q →
 InductionInterface.Correct installed lhs rhs t old a baseX pF pR c I (lb+cb+rb) u := by
 intro m u
 induction u with
 | zero =>
  intro hu target producerTag hq hp ctx inputs fuel
  dsimp only
  intro hguard
  obtain ⟨J,hJ⟩ := CurrentStructuralProducerInventory.PrimitiveProof.leaf _ installed lhs rhs t old a _ I
  exact LeafProof.leaf installed lhs rhs t old a baseX pF pR c I lb cb rb hL .zero J
   target producerTag hJ hq hp ctx inputs fuel hguard
 | succ =>
  intro hu target producerTag hq hp ctx inputs fuel
  dsimp only
  intro hguard
  obtain ⟨J,hJ⟩ := CurrentStructuralProducerInventory.PrimitiveProof.leaf _ installed lhs rhs t old a _ I
  exact LeafProof.leaf installed lhs rhs t old a baseX pF pR c I lb cb rb hL .successor J
   target producerTag hJ hq hp ctx inputs fuel hguard
 | projection i =>
  intro hu target producerTag hq hp ctx inputs fuel
  dsimp only
  intro hguard
  obtain ⟨J,hJ⟩ := CurrentStructuralProducerInventory.PrimitiveProof.leaf _ installed lhs rhs t old a _ I
  exact LeafProof.leaf installed lhs rhs t old a baseX pF pR c I lb cb rb hL (.projection i) J
   target producerTag hJ hq hp ctx inputs fuel hguard
 | composition f g hf hg =>
  intro hu
  have hf' := hf (CurrentStructuralProducerInventory.OccurrenceProof.trans hu (.compositionFunction f g (.here f rfl)))
  have hg' := fun i => hg i (CurrentStructuralProducerInventory.OccurrenceProof.trans hu (.compositionArgument f g i (.here (g i) rfl)))
  exact CompositionProof.composition installed lhs rhs t old a baseX pF pR c I lb cb rb hC
   q inventoryTag hInventory f g hu hf' hg'
 | recursion f g hf hg =>
  intro hu target producerTag hq hp ctx inputs fuel
  dsimp only
  intro hguard
  have hf' := hf (CurrentStructuralProducerInventory.OccurrenceProof.trans hu (.recursionBase f g (.here f rfl)))
  have hg' := hg (CurrentStructuralProducerInventory.OccurrenceProof.trans hu (.recursionStep f g (.here g rfl)))
  have h := RecursionProof.recursionAt installed lhs rhs t old a baseX pF pR c I lb cb rb hR
   q inventoryTag hInventory f g hu hf' hg' target producerTag hq hp ctx inputs.head inputs.tail fuel hguard
  exact Eq.mp (congrArg
   (fun xs => Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
    (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
     (calculation (tags I.previous) target xs) (code producerTag target xs))))
   (List.Vector.cons_head_tail inputs)) h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionProof
