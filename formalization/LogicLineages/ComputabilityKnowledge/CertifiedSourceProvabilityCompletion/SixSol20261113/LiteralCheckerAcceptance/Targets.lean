module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries

/-- Actual core composition, with no native or validity assumptions. -/
def InternalCoreNormalization : Prop := ∀ n (p : Program n) (qtag ptag : Nat)
    (v l a : Program 1) (x : Program 3),
  (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker v l a x bound initial finalizer⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  ∀ ctx (index fuel context formula certificate : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (normalization qtag (qtag+iteratorOffset v l a x) (qtag+1) ptag index fuel context formula certificate))

/-- All runtime certificate codes; positive existential output witnesses are
proved, never assumed. Literal registered decoder/drop suppliers are actual
subtrees at the retained SAME tuple. No claim of MP/generalization closure. -/
def InternalCoreAcceptance : Prop := ∀ n (p : Program n) (qtag ptag ctag dtag droptag : Nat)
    (v l a : Program 1) (x : Program 3),
  (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker v l a x bound initial finalizer⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  ∀ ctx (index fuel context formula certificate : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (acceptance qtag (qtag+iteratorOffset v l a x) ptag ctag index fuel context formula certificate))

/-- Identical new literal-auxiliary SAME construction with every prior clause
retained and the actual closed core acceptance endpoint added. HB remains open. -/
def SameSourceCoreAcceptance : Prop :=
  ∃ (valid logical arithmetic : Program 1) (axiomProgram : Program 3)
    (appendOffset : Nat),
  ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
    (tagG : Nat) (pG : Program 6),
    let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
    let q0 := LiteralKernelSource.coreChecker valid logical arithmetic axiomProgram bound initial finalizer
    let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
    let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
    HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram ∧
    SixSol20261112.HistoryMachine.KernelProgram k ∧
    (∀ (state : SixSol20261112.HistoryMachine.State) (index fuel count : Nat),
      evaluate (SixSol20261112.HistoryMachine.iterator k) (count ::ᵥ Encodable.encode state ::ᵥ index ::ᵥ fuel ::ᵥ nil) =
        Encodable.encode ((SixSol20261112.HistoryMachine.transition index fuel)^[count] state)) ∧
    SixSol20261112.HistoryMachine.BoundProgram bound ∧
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
      (nodes root)[HistoryIteratorDrain.rightTag pF valid logical arithmetic axiomProgram bound initial finalizer]? = some ⟨1,HistoryDecoder.decoder true⟩ ∧
      Nonempty (Derivation (S pF pR q)
        (HistoryIteratorDrain.drainClause pF valid logical arithmetic axiomProgram bound initial finalizer)) ∧
      (nodes root)[boundTag pF valid logical arithmetic axiomProgram]? = some ⟨1,bound⟩ ∧
      (nodes root)[initialTag pF valid logical arithmetic axiomProgram]? = some ⟨1,initial⟩ ∧
      (nodes root)[finalizerTag pF valid logical arithmetic axiomProgram]? = some ⟨4,finalizer⟩ ∧
      Nonempty (Derivation (S pF pR q) (boundClause pF valid logical arithmetic axiomProgram)) ∧
      Nonempty (Derivation (S pF pR q) (initialClause pF valid logical arithmetic axiomProgram)) ∧
      Nonempty (Derivation (S pF pR q) (finishClause pF valid logical arithmetic axiomProgram)) ∧
      Nonempty (Derivation (S pF pR q) (failureClause pF valid logical arithmetic axiomProgram)) ∧
      Nonempty (Derivation (S pF pR q) (acceptanceClause pF valid logical arithmetic axiomProgram))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.Targets
