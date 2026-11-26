module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.NodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.ValidatorPackageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries

private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
 (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
   (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
 Nonempty (Derivation (S pF pR q) phi) :=
 GorbowTheoryProofProof.monotonicity _ _
   (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

/-- All structural descendants and all seven closed internal clauses at ONE
fixed tuple. The only hypothesis locates the existing actual append subtree;
it adds no mathematics or validity law to the retained package. -/
theorem validatorPackage (logical arithmetic : Program 1) (axiomProgram : Program 3)
 (appendOffset : Nat) (pF pR : Program 1)
 (hoff : (nodes (HistoryKernel.kernel valid logical arithmetic axiomProgram))[appendOffset]? =
   some ⟨2,HistoryAppend.append⟩) :
 Targets.ValidatorPackage logical arithmetic axiomProgram appendOffset pF pR := by
 let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
 let q0 := LiteralKernelSource.coreChecker valid logical arithmetic axiomProgram bound initial finalizer
 let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let fuelTag := GorbowNamedInternalProvability.checkerTag pF
 let itag := iteratorTag pF logical arithmetic axiomProgram
 let vtag := validityTag pF logical arithmetic axiomProgram
 let ftag := formulaTag vtag
 let ktag := LiteralKernelSource.kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer
 let atag := LiteralKernelSource.appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset
 let ptag := LiteralKernelSource.pairTag pF valid logical arithmetic axiomProgram bound initial finalizer
 let ctag := LiteralKernelSource.consTag pF valid logical arithmetic axiomProgram bound initial finalizer
 have ht : (nodes root)[fuelTag]? = some ⟨5,Fuel.verifier q0⟩ :=
   GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 have hkin : (nodes root)[ktag]? = some ⟨3,k⟩ :=
   LiteralKernelSource.InstallationProof.kernelInstalled root fuelTag valid logical arithmetic axiomProgram bound initial finalizer ht
 have hain : (nodes root)[atag]? = some ⟨2,HistoryAppend.append⟩ :=
   GorbowPRSubtree.Proof.lookupTransport 4 root ktag ⟨3,k⟩ appendOffset ⟨2,HistoryAppend.append⟩ hkin hoff
 obtain ⟨hpin,_,_,_,hcin⟩ := HistoryKernel.OptionProof.kernelNodes root ktag valid logical arithmetic axiomProgram hkin
 have hi : (nodes root)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator k⟩ :=
   NodeProof.iteratorNode pF pR logical arithmetic axiomProgram
 have hv : (nodes root)[vtag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩ :=
   HistoryTopProvenance.OccurrenceProof.actualValidityOccurrence valid logical arithmetic axiomProgram 4 root itag hi
 obtain ⟨hf,hl,hr,hs,he,hct,hpt⟩ := NodeProof.lineNodes root vtag hv
 refine ⟨hi,hv,hf,hl,hr,hs,he,hct,hpt,?_,?_,?_,?_,?_,?_,?_⟩
 · obtain ⟨hd⟩ := LiteralSyntaxValidator.BooleanProof.internalBoolean 4 root ftag hf 2 (.var 0) (.var 1)
   exact inSource pF pR q (booleanClause ftag) ⟨Fuel.Logic.closeAll hd⟩
 · obtain ⟨hd⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding 4 root vtag ftag ptag hv hf hpin
     3 (.var 0) (.var 1) (.var 2)
   exact inSource pF pR q (lineClause vtag ftag ptag) ⟨Fuel.Logic.closeAll hd⟩
 · obtain ⟨hd⟩ := LiteralSyntaxValidator.ImplicationProof.internalImplicationConclusion 4 root ftag atag ctag hf hain hcin
     3 (.var 0) (.var 1) (.var 2)
   exact inSource pF pR q (implicationClause ftag atag ctag) ⟨Fuel.Logic.closeAll hd⟩
 · obtain ⟨hd⟩ := LiteralSyntaxValidator.QuantifierProof.internalQuantifier 4 root ftag ctag hf hcin
     10 (Or.inl rfl) 2 (.var 0) (.var 1)
   exact inSource pF pR q (quantifierClause ftag ctag 10) ⟨Fuel.Logic.closeAll hd⟩
 · obtain ⟨hd⟩ := LiteralSyntaxValidator.QuantifierProof.internalQuantifier 4 root ftag ctag hf hcin
     11 (Or.inr rfl) 2 (.var 0) (.var 1)
   exact inSource pF pR q (quantifierClause ftag ctag 11) ⟨Fuel.Logic.closeAll hd⟩
 · obtain ⟨hd⟩ := LiteralSyntaxScan.FusionProof.internalFusion 4 root (scanTag vtag) atag hs hain
     4 (.var 0) (.var 1) (.var 2) (.var 3)
   exact inSource pF pR q (scanFusionClause (scanTag vtag) atag) ⟨Fuel.Logic.closeAll hd⟩
 · obtain ⟨hd⟩ := LiteralSyntaxScan.FrameProof.internalFrame 4 root (scanTag vtag) atag hs hain
     4 (.var 0) (.var 1) (.var 2) (.var 3)
   exact inSource pF pR q (scanFrameClause (scanTag vtag) atag) ⟨Fuel.Logic.closeAll hd⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.ValidatorPackageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.ValidatorPackageProof
