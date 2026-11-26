module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.NativeStatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.ComparisonProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.FailureProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.StatementChecks

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.RetainedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112 LiteralCheckerAuxiliaries

private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
    (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
      (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
    Nonempty (Derivation (S pF pR q) phi) :=
  GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

theorem constructRetained :
 ∃ (logical arithmetic : Program 1) (axiomProgram : Program 3) (appendOffset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6),
 Retained logical arithmetic axiomProgram appendOffset pF pR c tagCK pCK tagG pG := by
  obtain ⟨oldValid,logical,arithmetic,axiomProgram,oldLeaves⟩ := HistoryDispatcher.LeavesProof.constructLeaves
  have hleaves : HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram :=
    ⟨LiteralSyntaxValidator.NativeProof.nativeLine,oldLeaves.2⟩
  have hk := HistoryKernel.NativeProof.nativeKernel valid logical arithmetic axiomProgram hleaves
  obtain ⟨hbound,hinitial,hfinal⟩ := LiteralCheckerAuxiliaries.NativeProof.nativeAuxiliaries
  obtain ⟨offset,hoff⟩ := LiteralKernelSource.OccurrenceProof.appendOffset valid logical arithmetic axiomProgram
  let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
  let q0 := LiteralKernelSource.coreChecker valid logical arithmetic axiomProgram bound initial finalizer
  have hq0 : UniversalVerifier q0 :=
    SixSol20261112.HistoryMachine.NativeProof.sameNumericChecker k bound initial finalizer hk hbound hinitial hfinal
  let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
  have hq : UniversalVerifier q := Fuel.NativeProof.sameNumericChecker q0 hq0
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := InstalledProducer.Proof.programProducer q
  obtain ⟨pF,pR,c,tagCK,tagG,hA,hSyntax,hInstall,hFixed,hGInstall⟩ :=
    InstalledProducer.RegistryProof.actualRegistry q hq pCK hCK pG
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let fuelTag := GorbowNamedInternalProvability.checkerTag pF
  let ktag := LiteralKernelSource.kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer
  let atag := LiteralKernelSource.appendTag pF valid logical arithmetic axiomProgram bound initial finalizer offset
  let ptag := LiteralKernelSource.pairTag pF valid logical arithmetic axiomProgram bound initial finalizer
  let ctag := LiteralKernelSource.consTag pF valid logical arithmetic axiomProgram bound initial finalizer
  have ht : (nodes root)[fuelTag]? = some ⟨5,Fuel.verifier q0⟩ :=
    GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  have hkin : (nodes root)[ktag]? = some ⟨3,k⟩ :=
    LiteralKernelSource.InstallationProof.kernelInstalled root fuelTag valid logical arithmetic axiomProgram bound initial finalizer ht
  have hain : (nodes root)[atag]? = some ⟨2,HistoryAppend.append⟩ :=
    GorbowPRSubtree.Proof.lookupTransport 4 root ktag ⟨3,k⟩ offset ⟨2,HistoryAppend.append⟩ hkin hoff
  obtain ⟨hpin,hsin,hein,hdin,hcin⟩ :=
    HistoryKernel.OptionProof.kernelNodes root ktag valid logical arithmetic axiomProgram hkin
  refine ⟨logical,arithmetic,axiomProgram,offset,
    pF,pR,c,tagCK,pCK,tagG,pG,hleaves,hk,
    SixSol20261112.HistoryMachine.NativeProof.iteratorCalibration k hk,hbound,hinitial,hfinal,hoff,hq0,
    hA,hSyntax,hCK,hInstall,hFixed,hG,hGInstall,hkin,hain,hpin,hcin,?_,?_,?_,?_,?_,?_,?_⟩
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
    exact inSource pF pR q (LiteralKernelSource.stepClause pF valid logical arithmetic axiomProgram bound initial finalizer offset)
      ⟨Fuel.Logic.closeAll hd⟩
  · have hi := SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled root fuelTag k bound initial finalizer ht
    obtain ⟨hd⟩ := HistoryIteratorSuffix.IterationProof.internalIteratorSuffix valid logical arithmetic axiomProgram 4 root
      (SixSol20261112.HistoryMachine.iteratorTag fuelTag k bound initial finalizer) atag ptag ctag hi hain hpin hcin 8
      (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7)
    exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
  · obtain ⟨dropOffset,hdrop⟩ := HistoryIteratorDrain.InstallationProof.dropOffset
    have hdropRoot : (nodes root)[atag+dropOffset]? = some ⟨2,HistoryLookup.drop⟩ :=
      GorbowPRSubtree.Proof.lookupTransport 4 root atag ⟨2,HistoryAppend.append⟩ dropOffset ⟨2,HistoryLookup.drop⟩ hain hdrop
    have hright := HistoryIteratorDrain.InstallationProof.rightInstalled root ktag valid logical arithmetic axiomProgram hkin
    have hcore := LiteralCheckerAuxiliaries.InstallationProof.coreInstalled root fuelTag q0 ht
    have hfinalNode : (nodes root)[finalizerTag pF valid logical arithmetic axiomProgram]? = some ⟨4,finalizer⟩ :=
      Fuel.Equations.functionChild root _ finalizer (SixSol20261112.HistoryMachine.checkerArguments k bound initial) hcore
    have hloop := Fuel.Equations.argumentChild root (coreTag pF valid logical arithmetic axiomProgram) finalizer
      (SixSol20261112.HistoryMachine.checkerArguments k bound initial) hcore 0
    have hboundNode : (nodes root)[boundTag pF valid logical arithmetic axiomProgram]? = some ⟨1,bound⟩ :=
      Fuel.Equations.functionChild root _ bound (fun _ : Fin 1 => .projection (4 : Fin 5))
        (Fuel.Equations.argumentChild root (loopTag pF valid logical arithmetic axiomProgram)
          (SixSol20261112.HistoryMachine.iterator k) (SixSol20261112.HistoryMachine.loopArguments bound initial) hloop 0)
    have hinitialNode : (nodes root)[initialTag pF valid logical arithmetic axiomProgram]? = some ⟨1,initial⟩ :=
      Fuel.Equations.functionChild root _ initial (fun _ : Fin 1 => .projection (4 : Fin 5))
        (Fuel.Equations.argumentChild root (loopTag pF valid logical arithmetic axiomProgram)
          (SixSol20261112.HistoryMachine.iterator k) (SixSol20261112.HistoryMachine.loopArguments bound initial) hloop 1)
    refine ⟨dropOffset,hdrop,hdropRoot,hright,?_,hboundNode,hinitialNode,hfinalNode,?_,?_,?_,?_⟩
    · have hi := SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled root fuelTag k bound initial finalizer ht
      obtain ⟨hd⟩ := HistoryIteratorDrain.IterationProof.internalIteratorDrain valid logical arithmetic axiomProgram 4 root
        (SixSol20261112.HistoryMachine.iteratorTag fuelTag k bound initial finalizer)
        (HistoryIteratorDrain.rightTag pF valid logical arithmetic axiomProgram bound initial finalizer)
        (atag+dropOffset) ptag ctag hi hright hdropRoot hpin hcin 4 (.var 0) (.var 1) (.var 2) (.var 3)
      exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
    · obtain ⟨hd⟩ := InitialProof.internalBound 4 root (boundTag pF valid logical arithmetic axiomProgram) hboundNode 1 (.var 0)
      exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
    · obtain ⟨hd⟩ := InitialProof.internalInitial 4 root (initialTag pF valid logical arithmetic axiomProgram) ptag hinitialNode hpin 1 (.var 0)
      exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
    · obtain ⟨hd⟩ := ComparisonProof.internalFinishCharacterization 4 root (finalizerTag pF valid logical arithmetic axiomProgram) ptag ctag
        hfinalNode hpin hcin 7 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
      exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
    · obtain ⟨hd⟩ := FailureProof.internalFinishFailure 4 root (finalizerTag pF valid logical arithmetic axiomProgram) ptag
        hfinalNode hpin 4 (.var 0) (.var 1) (.var 2) (.var 3)
      exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.RetainedProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.RetainedProof
