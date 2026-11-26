module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries
/-- Actual numeral and original validator scanner nodes, plus closed internal
syntax laws in the same source. No internal producer correctness or HB3. -/
def NumeralPackage (l a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (ntag : Nat) : Prop :=
 let x := SaturatedAxiomLeaf.saturated baseX
 let v := LiteralSourceCoreMP.valid
 let q := LiteralKernelSource.verifier v l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let stag := LiteralValidatedSource.scanTag (LiteralValidatedSource.validityTag pF l a x)
 let atag := LiteralKernelSource.appendTag pF v l a x bound initial finalizer offset
 let ptag := LiteralKernelSource.pairTag pF v l a x bound initial finalizer
 let ctag := LiteralKernelSource.consTag pF v l a x bound initial finalizer
 (nodes root)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩ ∧
 (nodes root)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ ∧
 Nonempty (Derivation (S pF pR q) (scanClause ntag stag ptag ctag)) ∧
 Nonempty (Derivation (S pF pR q) (continuationClause ntag stag ptag ctag atag))
/-- A NEW cumulative source selection retains all seven accepted packages at
ONE common tuple. No identity with a previous existential tuple, HB3, full
SelectedCertifiedPresentation or numbered completion is asserted. -/
def SameNumeralSourceHB2 : Prop :=
 ∃ (l a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag ntag : Nat),
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 LiteralValidatedSource.Targets.ValidatorPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a (SaturatedAxiomLeaf.saturated baseX) pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l a baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l a baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l a baseX pF pR c ∧
 NumeralPackage l a baseX offset pF pR ntag
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.Targets
