module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112

/-- Internal PA surjectivity of the ACTUAL registered square-shell pair AST. -/
def InternalPairSurjective : Prop := ∀ n (p : Program n) ptag,
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (code : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (pairSurjective ptag code))

/-- Converse to pair-image inverse: no pair-image premise on code. -/
def InternalDecoderReconstruction : Prop := ∀ n (p : Program n) ptag ltag rtag,
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩ →
  (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩ → ∀ ctx (code : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (HistoryKernel.pairCall ptag (call ltag (code ::ᵥ nil))
      (call rtag (code ::ᵥ nil))) code))

/-- Every positive raw list code reconstructs; no external coded-list witness. -/
def InternalListReconstruction : Prop := ∀ n (p : Program n) ctag htag ttag,
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩ →
  (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩ → ∀ ctx (code : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (HistoryKernel.pairCall ctag (call htag (.succ code ::ᵥ nil))
      (call ttag (.succ code ::ᵥ nil))) (.succ code)))

/-- Genuine runtime successful-prefix transport on the installed literal
iterator. No native calibration, validity, length, or reconstruction premise. -/
def InternalIteratorSuffix : Prop := ∀ (valid logical arithmetic : Program 1) (axiomProgram : Program 3),
  ∀ n (p : Program n) itag atag ptag ctag,
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel valid logical arithmetic axiomProgram)⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  ∀ ctx (count index fuel h tail lines out rest : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (iteratorSuffix itag atag ptag count index fuel h tail lines out rest))

/-- All previously accepted literal-source obligations are retained at the
IDENTICAL existential witnesses; only the iterator clause is appended. This
is not HB2/HB3 or certificate-constructor/finalizer closure. -/
def SameSourceIteratorSuffix : Prop :=
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
      (iteratorClause pF valid logical arithmetic axiomProgram bound initial finalizer appendOffset))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.Targets
