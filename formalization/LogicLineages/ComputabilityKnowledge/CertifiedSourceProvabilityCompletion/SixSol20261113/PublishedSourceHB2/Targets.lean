module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries
/-- Stronger-than-D placement of the original external-sentence HB2 schema.
The finite S-scheme proof may be constructively certified for each external
sentence triple. No internal numeric logical-leaf reflection principle is
assumed, and existential checker fuel/certificate witnesses remain internal. -/
def HB2Package (l a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code) : Prop :=
 let q := LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a
  (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer
 ∀ sigma tau : Sentence, Nonempty (Derivation (S pF pR q) (hb2Clause pF c sigma tau))

/-- The SAME already-saturated witnesses and all SIX previous packages are
retained literally. Only HB2 in S is added. No replacement source, source
identity with an older opaque tuple, HB3, selected full HB package, collapse,
or numbered completion follows from this target alone. -/
def SameSourceHB2 : Prop :=
 ∃ (l a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 LiteralValidatedSource.Targets.ValidatorPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a (SaturatedAxiomLeaf.saturated baseX) pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l a baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l a baseX offset pF pR mtag ∧
 HB2Package l a baseX pF pR c
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Targets
