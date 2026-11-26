module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries
/-- The actual installed axiom wrapper and its closed law in the rebuilt S.
An unrelated program having the same native semantics cannot satisfy the
literal node equality for this exact saturated AST. -/
def AxiomPackage (l a : Program 1) (baseX : Program 3) (pF pR : Program 1) (xtag : Nat) : Prop :=
 let x := SaturatedAxiomLeaf.saturated baseX
 let q := LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 (nodes root)[xtag]? = some ⟨3,SaturatedAxiomLeaf.saturated baseX⟩ ∧
 Nonempty (Derivation (S pF pR q) (axiomMonotonicityClause xtag))

/-- A NEW source selection after replacing the axiom leaf by its literal
saturation. No identity with an earlier source tuple is asserted. The four
previous package definitions themselves are unchanged and all refer to the
SAME new witnesses and the SAME explicit saturated axiom AST. Base calibration
is retained separately; it is never used as an internal monotonicity premise. -/
def SameSaturatedSource : Prop :=
 ∃ (l a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 LiteralValidatedSource.Targets.ValidatorPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a (SaturatedAxiomLeaf.saturated baseX) pF pR ∧
 AxiomPackage l a baseX pF pR xtag
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Targets
