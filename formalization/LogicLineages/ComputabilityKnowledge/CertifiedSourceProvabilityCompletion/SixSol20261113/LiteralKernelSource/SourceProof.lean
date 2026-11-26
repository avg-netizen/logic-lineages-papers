module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.InstallationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112

private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
    (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
      (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
    Nonempty (Derivation (S pF pR q) phi) :=
  GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

theorem sameSourceLiteralKernel : Targets.SameSourceLiteralKernel := by
  obtain ⟨valid,logical,arithmetic,axiomProgram,hleaves⟩ := HistoryDispatcher.LeavesProof.constructLeaves
  have hk := HistoryKernel.NativeProof.nativeKernel valid logical arithmetic axiomProgram hleaves
  obtain ⟨unusedKernel,bound,initial,finalizer,unusedCalibration,hbound,hinitial,hfinal⟩ :=
    SixSol20261112.HistoryMachine.NativeProgramsProof.nativePrograms
  obtain ⟨offset,hoff⟩ := OccurrenceProof.appendOffset valid logical arithmetic axiomProgram
  let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
  let q0 := coreChecker valid logical arithmetic axiomProgram bound initial finalizer
  have hq0 : UniversalVerifier q0 :=
    SixSol20261112.HistoryMachine.NativeProof.sameNumericChecker k bound initial finalizer hk hbound hinitial hfinal
  let q := verifier valid logical arithmetic axiomProgram bound initial finalizer
  have hq : UniversalVerifier q := Fuel.NativeProof.sameNumericChecker q0 hq0
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := InstalledProducer.Proof.programProducer q
  obtain ⟨pF,pR,c,tagCK,tagG,hA,hSyntax,hInstall,hFixed,hGInstall⟩ :=
    InstalledProducer.RegistryProof.actualRegistry q hq pCK hCK pG
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let fuelTag := GorbowNamedInternalProvability.checkerTag pF
  let ktag := kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer
  let atag := appendTag pF valid logical arithmetic axiomProgram bound initial finalizer offset
  let ptag := pairTag pF valid logical arithmetic axiomProgram bound initial finalizer
  let ctag := consTag pF valid logical arithmetic axiomProgram bound initial finalizer
  have ht : (nodes root)[fuelTag]? = some ⟨5,Fuel.verifier q0⟩ :=
    GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  have hkin : (nodes root)[ktag]? = some ⟨3,k⟩ :=
    InstallationProof.kernelInstalled root fuelTag valid logical arithmetic axiomProgram bound initial finalizer ht
  have hain : (nodes root)[atag]? = some ⟨2,HistoryAppend.append⟩ :=
    GorbowPRSubtree.Proof.lookupTransport 4 root ktag ⟨3,k⟩ offset ⟨2,HistoryAppend.append⟩ hkin hoff
  obtain ⟨hpin,hsin,hein,hdin,hcin⟩ :=
    HistoryKernel.OptionProof.kernelNodes root ktag valid logical arithmetic axiomProgram hkin
  refine ⟨valid,logical,arithmetic,axiomProgram,bound,initial,finalizer,offset,
    pF,pR,c,tagCK,pCK,tagG,pG,hleaves,hk,hbound,hinitial,hfinal,hoff,hq0,
    hA,hSyntax,hCK,hInstall,hFixed,hG,hGInstall,hkin,hain,hpin,hcin,?_,?_,?_,?_,?_⟩
  · obtain ⟨hd⟩ := Fuel.StepProof.openStep 4 root fuelTag q0 ht 5
      (.var 4) (.var 0) (.var 3) (.var 2) (.var 1)
    exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
  · obtain ⟨hd⟩ := Fuel.InductionProof.openIncrement 4 root fuelTag q0 ht 5
      (.var 4) (.var 0) (.var 3) (.var 2) (.var 1)
    have hclosed := Fuel.Logic.closeAll (n := 5)
      (phi := .all (Fuel.incrementTemplate fuelTag (.var 4 : Term 5) (.var 0)
        (.var 3) (.var 2) (.var 1))) hd
    exact inSource pF pR q (Fuel.incrementClause pF) ⟨hclosed⟩
  · obtain ⟨hd⟩ := Fuel.InductionProof.openMonotonicity 4 root fuelTag q0 ht 6
      (.var 5) (.var 1) (.var 0) (.var 4) (.var 3) (.var 2)
    exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
  · have hi := SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled root fuelTag k bound initial finalizer ht
    obtain ⟨hd⟩ := SixSol20261113.HistoryMachine.FusionProof.openFusion 4 root
      (SixSol20261112.HistoryMachine.iteratorTag fuelTag k bound initial finalizer) k hi 4
      (.var 0) (.var 1) (.var 2) (.var 3)
    have hclosed := Fuel.Logic.closeAll (n := 4)
      (phi := .all (SixSol20261112.HistoryMachine.fusionTemplate
        (SixSol20261112.HistoryMachine.iteratorTag fuelTag k bound initial finalizer)
        (.var 0 : Term 4) (.var 1) (.var 2) (.var 3))) hd
    exact inSource pF pR q (SixSol20261112.HistoryMachine.fusionClause pF k bound initial finalizer) ⟨hclosed⟩
  · obtain ⟨hd⟩ := HistoryKernel.SuffixProof.internalStepSuffix valid logical arithmetic axiomProgram
      4 root ktag atag ptag ctag hkin hain hpin hcin 7
      (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
    exact inSource pF pR q (stepClause pF valid logical arithmetic axiomProgram bound initial finalizer offset)
      ⟨Fuel.Logic.closeAll hd⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.SourceProof
