module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112

/-- Actual repeated-tail program exhausts every raw code within that code's
numerical bound. The weak bound is internal existential arithmetic. -/
def InternalDropExhaustion : Prop := ∀ n (p : Program n) (tag : Nat),
  (nodes p)[tag]? = some ⟨2,HistoryLookup.drop⟩ → ∀ ctx (count lines : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (HistoryBounds.weakBound lines count) (.equal (dropCall tag count lines) .zero)))

/-- Exact remaining-lines evolution on the actual kernel iterator. Applies to
NONE, SOME, successful and failing steps alike; no native calibration premise. -/
def InternalIteratorRemaining : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag dtag dropTag ptag ctag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (count option lines index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (remainingCall dtag itag ptag count option lines index fuel) (dropCall dropTag count lines)))

/-- No success or validity restriction: encoded-code-many steps leave no lines. -/
def InternalIteratorDrain : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag dtag dropTag ptag ctag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (option lines index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (remainingCall dtag itag ptag lines option lines index fuel) .zero))

/-- Retains every accepted SAME-source witness and clause, adding only actual
drop occurrence/installation and iterator drain. Opaque auxiliary bound,
initializer and finalizer internal correctness remains an explicit unpaid gap. -/
def SameSourceIteratorDrain : Prop :=
  ∃ (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (bound initial : Program 1) (finalizer : Program 4) (appendOffset : Nat),
  ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
    (tagG : Nat) (pG : Program 6),
    let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
    let q0 := LiteralKernelSource.coreChecker valid logical arithmetic axiomProgram bound initial finalizer
    let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
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
    (nodes root)[LiteralKernelSource.kernelTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨3,k⟩ ∧
    (nodes root)[LiteralKernelSource.appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset]? = some ⟨2,HistoryAppend.append⟩ ∧
    (nodes root)[LiteralKernelSource.pairTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨2,HistoryCodec.pair⟩ ∧
    (nodes root)[LiteralKernelSource.consTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨2,HistoryCodec.cons⟩ ∧
    Nonempty (Derivation (S pF pR q) (Fuel.stepClause pF)) ∧
    Nonempty (Derivation (S pF pR q) (Fuel.incrementClause pF)) ∧
    Nonempty (Derivation (S pF pR q) (Fuel.monotonicityClause pF)) ∧
    Nonempty (Derivation (S pF pR q) (SixSol20261112.HistoryMachine.fusionClause pF k bound initial finalizer)) ∧
    Nonempty (Derivation (S pF pR q)
      (LiteralKernelSource.stepClause pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset)) ∧
    Nonempty (Derivation (S pF pR q)
      (HistoryIteratorSuffix.iteratorClause pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset)) ∧
    ∃ dropOffset : Nat,
      (nodes HistoryAppend.append)[dropOffset]? = some ⟨2,HistoryLookup.drop⟩ ∧
      (nodes root)[LiteralKernelSource.appendTag pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset+dropOffset]? = some ⟨2,HistoryLookup.drop⟩ ∧
      (nodes root)[rightTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨1,HistoryDecoder.decoder true⟩ ∧
      Nonempty (Derivation (S pF pR q)
        (drainClause pF valid logical arithmetic axiomProgram bound initial finalizer))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.Targets
