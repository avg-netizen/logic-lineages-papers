module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112

/-- Construct a NEW SAME-source tuple, retaining every original source/CK/
producer/fuel/fusion obligation. Its kernel is the literal calibrated AST,
not the prior opaque existential witness. The append supplier must occur in
that kernel's actual nodes; no padding or unrelated installed helper suffices.
This adds a genuine step law, not HB2/HB3 or full iterator extension. -/
def SameSourceLiteralKernel : Prop :=
  ∃ (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) (appendOffset : Nat),
  ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
    (tagG : Nat) (pG : Program 6),
    let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
    let q0 := coreChecker valid logical arithmetic axiomProgram bound initial finalizer
    let q := verifier valid logical arithmetic axiomProgram bound initial finalizer
    let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
    HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram ∧
    SixSol20261112.HistoryMachine.KernelProgram k ∧ SixSol20261112.HistoryMachine.BoundProgram bound ∧
    SixSol20261112.HistoryMachine.InitialProgram initial ∧ SixSol20261112.HistoryMachine.FinishProgram finalizer ∧
    (nodes k)[appendOffset]? = some ⟨2,HistoryAppend.append⟩ ∧
    UniversalVerifier q0 ∧ Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram pCK ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tagCK pCK ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tagCK ∧
    InstalledProducer.ProducerFor q pG ∧ InstalledProducer.RegistryInstall pF pR q tagG pG ∧
    (nodes root)[kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨3,k⟩ ∧
    (nodes root)[appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset]? = some ⟨2,HistoryAppend.append⟩ ∧
    (nodes root)[pairTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨2,HistoryCodec.pair⟩ ∧
    (nodes root)[consTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨2,HistoryCodec.cons⟩ ∧
    Nonempty (Derivation (S pF pR q) (Fuel.stepClause pF)) ∧
    Nonempty (Derivation (S pF pR q) (Fuel.incrementClause pF)) ∧
    Nonempty (Derivation (S pF pR q) (Fuel.monotonicityClause pF)) ∧
    Nonempty (Derivation (S pF pR q) (SixSol20261112.HistoryMachine.fusionClause pF k bound initial finalizer)) ∧
    Nonempty (Derivation (S pF pR q)
      (stepClause pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.Targets
