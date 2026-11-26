module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.InductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB

private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
    (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
      (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
    Nonempty (Derivation (S pF pR q) phi) :=
  GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

theorem sameSourceFuelInvariant : Targets.SameSourceFuelInvariant := by
  obtain ⟨q0,hq0⟩ := GorbowEnumeratedProvability.Proof.fixedUniversalProgram
  let q := verifier q0
  have hq : UniversalVerifier q := NativeProof.sameNumericChecker q0 hq0
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := InstalledProducer.Proof.programProducer q
  obtain ⟨pF,pR,c,tagCK,tagG,hA,hSyntax,hInstall,hFixed,hGInstall⟩ :=
    InstalledProducer.RegistryProof.actualRegistry q hq pCK hCK pG
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let tag := GorbowNamedInternalProvability.checkerTag pF
  have ht : (nodes root)[tag]? = some ⟨5,verifier q0⟩ :=
    GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  refine ⟨q0,pF,pR,c,tagCK,pCK,tagG,pG,hq0,hA,hSyntax,hCK,hInstall,hFixed,hG,hGInstall,?_,?_,?_⟩
  · obtain ⟨hd⟩ := StepProof.openStep 4 root tag q0 ht 5
      (.var 4) (.var 0) (.var 3) (.var 2) (.var 1)
    exact inSource pF pR q _ ⟨Logic.closeAll hd⟩
  · obtain ⟨hd⟩ := InductionProof.openIncrement 4 root tag q0 ht 5
      (.var 4) (.var 0) (.var 3) (.var 2) (.var 1)
    exact inSource pF pR q _ ⟨Logic.closeAll hd⟩
  · obtain ⟨hd⟩ := InductionProof.openMonotonicity 4 root tag q0 ht 6
      (.var 5) (.var 1) (.var 0) (.var 4) (.var 3) (.var 2)
    exact inSource pF pR q _ ⟨Logic.closeAll hd⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Proof
