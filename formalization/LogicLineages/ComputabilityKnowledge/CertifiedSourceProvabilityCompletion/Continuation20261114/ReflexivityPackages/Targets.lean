module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityPackages.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityPackages.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
open SixSol20261113.LiteralCheckerAuxiliaries
/-- Universal same-witness assembly: no source re-selection inside this bridge. -/
def FixedWitnessIntegration : Prop :=
 ∀ (old a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
 (tagG : Nat) (pG : Program 6) (mtag : Nat),
 LiteralValidatedSource.Retained (ReflexivitySource.logical old) a
  (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG →
 (nodes (GorbowSourceRegistryPadding.root
  (augmented pF (LiteralKernelSource.verifier LiteralSourceCoreMP.valid
   (ReflexivitySource.logical old) a (SaturatedAxiomLeaf.saturated baseX)
   bound initial finalizer)) pR))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ →
 ∃ xtag, Packages old a baseX offset pF pR c mtag xtag
/-- Entire retained source/CK/producer plus every accepted saturated-source,
validator, MP, fuel, axiom, closure and published HB2 package at identical NEW
witnesses selected with explicit logical refinement. No old source identity,
quotation installation, coherent computation, HB3 or numbered completion. -/
def SameReflexivitySource : Prop :=
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (ReflexivitySource.logical old) a
  (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 Packages old a baseX offset pF pR c mtag xtag
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityPackages.Targets
