module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev logical (old : Program 1) : Program 1 := UniformClosedRule13.logicalLeaf old
abbrev verifier (old a : Program 1) (baseX : Program 3) : Program 5 :=
 UniformClosedRule13Certificate.verifier old a (SaturatedAxiomLeaf.saturated baseX)
abbrev root (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier old a baseX)) pR
/-- Fixed before source tuple and global tags; no tag appears in this AST. -/
def extra (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨4,LiteralRawMP.constructor⟩,
  ⟨6,UniformClosedRule13Registry.carrier old a (SaturatedAxiomLeaf.saturated baseX)⟩]
/-- Six existing source packages at the SAME newly chosen source tuple. -/
def Packages (old a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (mtag xtag : Nat) : Prop :=
 let l := logical old
 let x := SaturatedAxiomLeaf.saturated baseX
 LiteralValidatedSource.Targets.ValidatorPackage l a x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l a x offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l a x pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l a baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l a baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l a baseX pF pR c
/-- Actual-root installed witnesses, with derivations in the new published S.
No Theory(carrier) cast or equality with an earlier source tuple. -/
def RuntimeCapability (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : UniformClosedRule13Certificate.Installation (root pF pR old a baseX)
  old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (formula replacement index fuel : Term ctx),
 let C := UniformClosedRule13.conclusionValue I.caseTag I.predTag I.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.ctag I.constructorTag formula replacement
 Nonempty (Derivation (S pF pR (verifier old a baseX))
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag formula replacement)
   (.conj
    (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code)
     (UniformClosedRule13Certificate.output I.ptag I.ctag I.caseTag I.predTag formula replacement))
    (.conj
     (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source
