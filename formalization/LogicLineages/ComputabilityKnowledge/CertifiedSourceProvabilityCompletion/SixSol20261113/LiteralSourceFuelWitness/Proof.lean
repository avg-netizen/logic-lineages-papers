module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112 LiteralCheckerAuxiliaries
private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
 (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
   (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
 Nonempty (Derivation (S pF pR q) phi) :=
 GorbowTheoryProofProof.monotonicity _ _
   (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

/-- The two actual addresses are derived from the unchanged source root;
no extra semantic premise is required for either clause. -/
theorem witnessPackage (l a : Program 1) (x : Program 3) (pF pR : Program 1) :
 Targets.WitnessPackage l a x pF pR := by
 let valid := LiteralSourceCoreMP.valid
 let q0 := LiteralKernelSource.coreChecker valid l a x bound initial finalizer
 let q := LiteralKernelSource.verifier valid l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let vtag := GorbowNamedInternalProvability.checkerTag pF
 let qtag := LiteralSourceCoreMP.coreTag pF l a x
 have hv : (nodes root)[vtag]? = some ⟨5,Fuel.verifier q0⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 have hq : (nodes root)[qtag]? = some ⟨5,q0⟩ :=
  LiteralSourceCoreMP.NodeProof.coreInstalled pF pR l a x
 obtain ⟨hex⟩ := FuelWitness.StatementChecks.exactExtraction 4 root vtag qtag q0 hv hq 5
  (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
 obtain ⟨hin⟩ := FuelWitness.StatementChecks.exactInjection 4 root vtag qtag q0 hv hq 5
  (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
 exact ⟨inSource pF pR q (extractionClause vtag qtag) ⟨Fuel.Logic.closeAll hex⟩,
  inSource pF pR q (injectionClause vtag qtag) ⟨Fuel.Logic.closeAll hin⟩⟩

/-- Literal reuse of the accepted existential witnesses, not a new source
construction or an equality asserted between separately chosen sources. -/
theorem sameSourceFuelWitness : Targets.SameSourceFuelWitness := by
 obtain ⟨l,a,x,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,hret,hval,hmp⟩ :=
  LiteralSourceCoreMP.StatementChecks.exactSourceCoreMP
 exact ⟨l,a,x,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,hret,hval,hmp,
  witnessPackage l a x pF pR⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceFuelWitness.Proof
