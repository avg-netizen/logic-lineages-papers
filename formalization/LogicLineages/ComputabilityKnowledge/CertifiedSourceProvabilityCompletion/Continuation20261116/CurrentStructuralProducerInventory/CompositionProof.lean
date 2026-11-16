module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.ExtractionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.OccurrenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CompositionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem installed {arity k n m j : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (q : Program n) (carrierTag : Nat)
 (hc : (nodes p)[carrierTag]? = some ⟨6,carrier installed lhs rhs t old a baseX q⟩)
 (f : Program j) (g : Fin j → Program m) (hu : Occurs ⟨m,.composition f g⟩ q)
 (target producerTag : Nat) (hq : (nodes p)[target]? = some ⟨m,.composition f g⟩) :
 InstalledAt p installed lhs rhs t old a baseX target producerTag (.composition f g) := by
 classical
 have hfOcc : Occurs (⟨j,f⟩ : Packed) q :=
  OccurrenceProof.trans hu (.compositionFunction f g (.here f rfl))
 have hgOcc : ∀ i, Occurs (⟨m,g i⟩ : Packed) q := fun i =>
  OccurrenceProof.trans hu (.compositionArgument f g i (.here (g i) rfl))
 obtain ⟨FTag,hF⟩ := ExtractionProof.compiledNode p installed lhs rhs t old a baseX q carrierTag hc f hfOcc
 have hGs := fun i => ExtractionProof.compiledNode p installed lhs rhs t old a baseX q carrierTag hc (g i) (hgOcc i)
 choose GTags hG using hGs
 let J : CurrentCompositionProducerProgram.Tags j :=
  {C := PrescribedRuntimeCallCongruence.tags I.previous,
   ptag := I.currentK.ptag,r13 := I.previous.previous.current.constructorTag,
   functionTag := target+1,argumentTags := fun i => target+GorbowPRChildTags.argumentTag f g i,
   functionProducerTag := FTag,argumentProducerTags := GTags}
 refine ⟨J,?_,rfl,fun _ => rfl⟩
 exact {
  primitives := CurrentCompositionProducerCore.OriginalProof.installed p installed lhs rhs t old a _ I,
  hp := I.currentK.h_ptag,h13 := I.previous.previous.current.h_constructor,
  hf := SixSol20261112.Fuel.Equations.functionChild p target f g hq,
  hg := SixSol20261112.Fuel.Equations.argumentChild p target f g hq,
  hF := hF,hG := hG}

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CompositionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CompositionProof
