module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries
/-- Three additional closed laws in the SAME already-saturated source, using
its actual core, outer verifier, append, cons and original MP constructor. -/
def ClosurePackage (l a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (mtag : Nat) : Prop :=
 let x := SaturatedAxiomLeaf.saturated baseX
 let v := LiteralSourceCoreMP.valid
 let q := LiteralKernelSource.verifier v l a x bound initial finalizer
 let vtag := GorbowNamedInternalProvability.checkerTag pF
 let qtag := LiteralSourceCoreMP.coreTag pF l a x
 let atag := LiteralKernelSource.appendTag pF v l a x bound initial finalizer offset
 let ctag := LiteralKernelSource.consTag pF v l a x bound initial finalizer
 Nonempty (Derivation (S pF pR q) (coreMonotonicityClause qtag)) ∧
 Nonempty (Derivation (S pF pR q) (equivalenceClause vtag qtag)) ∧
 Nonempty (Derivation (S pF pR q) (outerMPClause vtag atag ctag mtag))

/-- Retains all five accepted packages LITERALLY at IDENTICAL saturated-source
witnesses, including base calibration, original producer/install and axiom
node/law. Adds only the three closed laws. No new source selection, old-opaque
source identity, rho-distribution, HB2/HB3 or numbered completion is asserted. -/
def SameSourceMP : Prop :=
 ∃ (l a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 LiteralValidatedSource.Targets.ValidatorPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a (SaturatedAxiomLeaf.saturated baseX) pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l a baseX pF pR xtag ∧
 ClosurePackage l a baseX offset pF pR mtag
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.Targets
