module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivitySource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityPackages
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
/-- Exactly the six previously accepted downstream packages at one fixed
refined-logical, saturated-axiom source. Retained (including CK) remains separate. -/
def Packages (old a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (mtag xtag : Nat) : Prop :=
 let l := ReflexivitySource.logical old
 let x := SaturatedAxiomLeaf.saturated baseX
 LiteralValidatedSource.Targets.ValidatorPackage l a x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a x offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a x pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l a baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l a baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l a baseX pF pR c
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityPackages
