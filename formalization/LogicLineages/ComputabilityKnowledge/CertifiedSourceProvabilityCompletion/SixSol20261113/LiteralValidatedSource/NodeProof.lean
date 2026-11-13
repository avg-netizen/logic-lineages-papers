module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.NodeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries HistoryRuleSuffix

theorem lineNodes {n : Nat} (p : Program n) (vtag : Nat)
 (hv : (nodes p)[vtag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩) :
 (nodes p)[formulaTag vtag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩ ∧
 (nodes p)[leftTag vtag]? = some ⟨1,HistoryDecoder.decoder false⟩ ∧
 (nodes p)[rightTag vtag]? = some ⟨1,HistoryDecoder.decoder true⟩ ∧
 (nodes p)[scanTag vtag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ ∧
 (nodes p)[equalityTag vtag]? = some ⟨2,equalCode⟩ ∧
 (nodes p)[taskConsTag vtag]? = some ⟨2,HistoryCodec.cons⟩ ∧
 (nodes p)[taskPairTag vtag]? = some ⟨2,HistoryCodec.pair⟩ := by
 have hf := Fuel.Equations.functionChild p vtag LiteralSyntaxValidator.formulaValidator lineArguments hv
 have hl := Fuel.Equations.argumentChild p vtag LiteralSyntaxValidator.formulaValidator lineArguments hv 0
 have hrw := Fuel.Equations.argumentChild p vtag LiteralSyntaxValidator.formulaValidator lineArguments hv 1
 have hr := Fuel.Equations.argumentChild p (lineRawTag vtag) (HistoryDecoder.decoder false)
   (fun _ : Fin 1 => HistoryDecoder.decoder true) hrw 0
 have he := Fuel.Equations.functionChild p (formulaTag vtag) equalCode formulaArguments hf
 have hsw := Fuel.Equations.argumentChild p (formulaTag vtag) equalCode formulaArguments hf 0
 have hs := Fuel.Equations.functionChild p (scanWrapper vtag) LiteralSyntaxScan.scanCode scanArguments hsw
 have hcw := Fuel.Equations.argumentChild p (scanWrapper vtag) LiteralSyntaxScan.scanCode scanArguments hsw 0
 have hc := Fuel.Equations.functionChild p (taskListWrapper vtag) HistoryCodec.cons taskArguments hcw
 have hpw := Fuel.Equations.argumentChild p (taskListWrapper vtag) HistoryCodec.cons taskArguments hcw 0
 have hp := Fuel.Equations.functionChild p
   (taskListWrapper vtag + argumentTag HistoryCodec.cons taskArguments 0)
   HistoryCodec.pair (Fin.cases (constant 2 1) (Fin.cases (.projection 0) Fin.elim0)) hpw
 exact ⟨hf,hl,hr,hs,he,hc,hp⟩

theorem iteratorNode (pF pR logical arithmetic : Program 1) (axiomProgram : Program 3) :
 let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 (nodes root)[iteratorTag pF logical arithmetic axiomProgram]? = some
   ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel valid logical arithmetic axiomProgram)⟩ := by
 let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
 let q0 := LiteralKernelSource.coreChecker valid logical arithmetic axiomProgram bound initial finalizer
 let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 have ht : (nodes root)[GorbowNamedInternalProvability.checkerTag pF]? = some ⟨5,Fuel.verifier q0⟩ :=
   GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 exact SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled root
   (GorbowNamedInternalProvability.checkerTag pF) k bound initial finalizer ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.NodeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.NodeProof
