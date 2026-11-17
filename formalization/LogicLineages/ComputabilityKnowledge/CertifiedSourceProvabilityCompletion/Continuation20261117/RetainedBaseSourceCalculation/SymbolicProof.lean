module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.SymbolicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence


open SixSol20261112.Fuel NamedArithmeticGraph

theorem peel {arity n ctx : Nat} (root : Program arity) (tag : Nat) (p : Program 1) (q : Program n)
 (h : (nodes root)[tag]? = some ⟨1,GorbowNamedInternalProvability.augment p q⟩) (value : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory root)
  (.equal (call tag (value ::ᵥ nil)) (call (tag+2) (value ::ᵥ nil)))) := by
 let branches := CorrectedAugmentationErasure.branches p q
 let values := List.Vector.ofFn (fun i => call (tag+argumentTag (.projection (0 : Fin 2)) branches i) (value ::ᵥ nil))
 obtain ⟨hc⟩ := Equations.compositionValues root tag (.projection (0 : Fin 2)) branches h (value ::ᵥ nil) values
  (by
   intro i
   simp only [values,List.Vector.get_ofFn]
   exact ⟨.logical (.reflexive _)⟩)
 have hp := Equations.functionChild root tag (.projection (0 : Fin 2)) branches h
 obtain ⟨he⟩ := Equations.projection root (tag+1) (0 : Fin 2) hp values
 exact ⟨Logic.trans _ _ _ hc he⟩

theorem nodes {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6) :
 let pF := RetainedBaseProducerInstallation.selected f lhs rhs t old a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 (GorbowPRRegistry.nodes root)[6]? = some ⟨1,augmented pF q⟩ ∧
 (GorbowPRRegistry.nodes root)[8]? = some ⟨1,pF⟩ ∧
 (GorbowPRRegistry.nodes root)[10]? = some ⟨1,GorbowNamedInternalProvability.augment pF0 pCK⟩ ∧
 (GorbowPRRegistry.nodes root)[12]? = some ⟨1,pF0⟩ := by
 let pF := RetainedBaseProducerInstallation.selected f lhs rhs t old a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let box := InstalledProducerExtra.container pG (RetainedBaseProducerInstallation.extra f lhs rhs t old a baseX pF0)
 have h6 : (GorbowPRRegistry.nodes root)[6]? = some ⟨1,augmented pF q⟩ :=
  GorbowSourceRegistryPadding.Proof.functionRoot (augmented pF q) pR
 have h8 : (GorbowPRRegistry.nodes root)[8]? = some ⟨1,pF⟩ :=
  RetainedBaseProducerInstallation.RegistryProof.firstChild root 6 pF q h6
 have h10 : (GorbowPRRegistry.nodes root)[10]? = some ⟨1,inner⟩ :=
  RetainedBaseProducerInstallation.RegistryProof.firstChild root 8 inner box h8
 have h12 : (GorbowPRRegistry.nodes root)[12]? = some ⟨1,pF0⟩ :=
  RetainedBaseProducerInstallation.RegistryProof.firstChild root 10 pF0 pCK h10
 exact ⟨h6,h8,h10,h12⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.SymbolicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.SymbolicProof
