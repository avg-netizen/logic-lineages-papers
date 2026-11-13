module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.FusionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HistoryMachine.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Proof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open GorbowPRChildTags
open SixSol20261112.HistoryMachine
open SixSol20261112

/-- Locate the actual iterator below the same saturating checker, not a separately
selected extensionally equal program. -/
theorem iteratorInstalled {n : Nat} (p : Program n) fuelTag
    (kernel : Program 3) (bound initial : Program 1) (finalizer : Program 4)
    (ht : (nodes p)[fuelTag]? = some ⟨5,Fuel.verifier (checker kernel bound initial finalizer)⟩) :
    (nodes p)[iteratorTag fuelTag kernel bound initial finalizer]? = some ⟨4,iterator kernel⟩ := by
  let q0 := checker kernel bound initial finalizer
  have hacc := Fuel.Equations.functionChild p fuelTag (Fuel.accumulator q0) Fuel.outerArguments ht
  have hbase : (nodes p)[fuelTag+2]? = some ⟨4,Fuel.base q0⟩ := by
    have h := GorbowPRSubtree.Proof.lookupTransport n p (fuelTag+1)
      ⟨5,Fuel.accumulator q0⟩ 1 ⟨4,Fuel.base q0⟩ hacc
      (GorbowPRChildTags.Proof.recursionBase 4 (Fuel.base q0) (Fuel.step q0))
    simpa only [Nat.add_assoc] using h
  have hinner := Fuel.Equations.argumentChild p (fuelTag+2) Fuel.isOne
    (fun _ : Fin 1 => Program.composition q0 Fuel.baseArguments) hbase 0
  have hq := Fuel.Equations.functionChild p
    (fuelTag+2+argumentTag Fuel.isOne (fun _ : Fin 1 => Program.composition q0 Fuel.baseArguments) 0)
    q0 Fuel.baseArguments hinner
  have hloop := Fuel.Equations.argumentChild p (coreCheckerTag fuelTag q0)
    finalizer (checkerArguments kernel bound initial) hq 0
  exact Fuel.Equations.functionChild p
    (coreCheckerTag fuelTag q0 + argumentTag finalizer (checkerArguments kernel bound initial) 0)
    (iterator kernel) (loopArguments bound initial) hloop

private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
    (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
      (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
    Nonempty (Derivation (S pF pR q) phi) :=
  GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

theorem sameSourceHistoryFusion : SixSol20261112.HistoryMachine.Targets.SameSourceHistoryFusion := by
  obtain ⟨kernel,bound,initial,finalizer,hkernel,hbound,hinitial,hfinal⟩ :=
    SixSol20261112.HistoryMachine.NativeProgramsProof.nativePrograms
  let q0 := checker kernel bound initial finalizer
  have hq0 : UniversalVerifier q0 :=
    SixSol20261112.HistoryMachine.NativeProof.sameNumericChecker
      kernel bound initial finalizer hkernel hbound hinitial hfinal
  let q := Fuel.verifier q0
  have hq : UniversalVerifier q := Fuel.NativeProof.sameNumericChecker q0 hq0
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := InstalledProducer.Proof.programProducer q
  obtain ⟨pF,pR,c,tagCK,tagG,hA,hSyntax,hInstall,hFixed,hGInstall⟩ :=
    InstalledProducer.RegistryProof.actualRegistry q hq pCK hCK pG
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let tag := GorbowNamedInternalProvability.checkerTag pF
  have ht : (nodes root)[tag]? = some ⟨5,Fuel.verifier q0⟩ :=
    GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  refine ⟨kernel,bound,initial,finalizer,pF,pR,c,tagCK,pCK,tagG,pG,
    hkernel,hbound,hinitial,hfinal,hq0,hA,hSyntax,hCK,hInstall,hFixed,hG,hGInstall,?_,?_,?_,?_⟩
  · obtain ⟨hd⟩ := Fuel.StepProof.openStep 4 root tag q0 ht 5
      (.var 4) (.var 0) (.var 3) (.var 2) (.var 1)
    exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
  · obtain ⟨hd⟩ := Fuel.InductionProof.openIncrement 4 root tag q0 ht 5
      (.var 4) (.var 0) (.var 3) (.var 2) (.var 1)
    exact inSource pF pR q (Fuel.incrementClause pF) ⟨Fuel.Logic.closeAll hd⟩
  · obtain ⟨hd⟩ := Fuel.InductionProof.openMonotonicity 4 root tag q0 ht 6
      (.var 5) (.var 1) (.var 0) (.var 4) (.var 3) (.var 2)
    exact inSource pF pR q _ ⟨Fuel.Logic.closeAll hd⟩
  · have hi := iteratorInstalled root tag kernel bound initial finalizer ht
    obtain ⟨hd⟩ := FusionProof.openFusion 4 root
      (iteratorTag tag kernel bound initial finalizer) kernel hi 4
      (.var 0) (.var 1) (.var 2) (.var 3)
    exact inSource pF pR q (fusionClause pF kernel bound initial finalizer)
      ⟨Fuel.Logic.closeAll hd⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryMachine.SourceProof
