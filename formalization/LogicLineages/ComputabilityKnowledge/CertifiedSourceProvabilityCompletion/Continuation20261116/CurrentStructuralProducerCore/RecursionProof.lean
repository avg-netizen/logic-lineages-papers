module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionInterface
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.RecursionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore
theorem recursionAt (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (lb cb rb : Nat)
 (hR : BoundInterfaces.Recursion installed lhs rhs t old a baseX pF pR c I rb)
 {n m : Nat} (q : Program n) (inventoryTag : Nat)
 (hInventory : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[inventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier installed lhs rhs t old a baseX q⟩)
 (f : Program m) (g : Program (m+2)) (hu : Occurs ⟨m+1,.recursion f g⟩ q)
 (hf : InductionInterface.Correct installed lhs rhs t old a baseX pF pR c I (lb+cb+rb) f)
 (hg : InductionInterface.Correct installed lhs rhs t old a baseX pF pR c I (lb+cb+rb) g)
 (target producerTag : Nat)
 (hq : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? = some ⟨m+1,.recursion f g⟩)
 (hp : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨m+2,CurrentStructuralProducerCompiler.compile (.recursion f g)⟩)
 (ctx : Nat) (counter : Term ctx) (inputs : List.Vector (Term ctx) m) (fuel : Term ctx)
 (hguard : Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (orderGuard (Term.numeral (lb+cb+rb)) fuel))) :
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
   (calculation (tags I.previous) target (counter ::ᵥ inputs)) (code producerTag target (counter ::ᵥ inputs)))) := by
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 obtain ⟨actualProducer,hActualProducer,R,hTarget,hPublic⟩ := CurrentStructuralProducerInventory.RecursionProof.installed
  p installed lhs rhs t old a baseX I q inventoryTag hInventory f g hu target hq
 subst target
 have hbase := hf (R.qTag+1) R.BTag R.hBase R.hB ctx inputs fuel hguard
 have hbaseCore := CoreTools.project U _ _ _ _ _ _ hbase
 let liftedInputs := inputs.map liftTerm
 have hstep := hg (R.qTag+stepTag f) R.GTag R.hStep R.hG (ctx+1)
  (stepInputs R.qTag (.var 0) liftedInputs) (liftTerm fuel)
  (GuardProof.lift U (lb+cb+rb) fuel hguard)
 obtain ⟨hstepCore⟩ := CoreTools.project U _ _ _ _ _ _ hstep
 have hstepCore' : Nonempty (Derivation U
  (core I.currentK.coreTag (liftTerm (Term.numeral (n := ctx) (Encodable.encode c))) (liftTerm fuel)
   (childFormula (tags I.previous) (R.qTag+stepTag f) (stepInputs R.qTag (.var 0) liftedInputs))
   (childCode R.GTag (R.qTag+stepTag f) (stepInputs R.qTag (.var 0) liftedInputs)))) := by
  simp only [liftTerm,GorbowFormulaSubstitution.renameTerm,Logic.substNumeral]
  exact ⟨hstepCore⟩
 have hacc := hR m f g (CurrentStructuralProducerCompiler.compile f) (CurrentStructuralProducerCompiler.compile g)
  R ctx inputs fuel counter (GuardProof.lower U lb cb rb fuel hguard).2.2 hbaseCore hstepCore'
 have hformula := FormulaBridge.actualFormula p installed lhs rhs t old a baseX I f g
  (CurrentStructuralProducerCompiler.compile f) (CurrentStructuralProducerCompiler.compile g) R counter inputs
 have hcode := GorbowPRInternalCoherence.Proof.registryCoherence 4 p R.producer.publicTag producerTag
  (m+2) (CurrentRecursionProducerProgram.program f g (CurrentStructuralProducerCompiler.compile f)
   (CurrentStructuralProducerCompiler.compile g)) R.producer.hpublic hp ctx
  (Term.numeral R.qTag ::ᵥ counter ::ᵥ inputs)
 exact CoreTools.transport p installed lhs rhs t old a _ I U
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX)
  _ _ _ _ _ _ hformula hcode hacc

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.RecursionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.RecursionProof
