module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112

/-- Exact ORIGINAL checked decoder, not merely existence of an Encodable preimage.
This native supplier separately pays the omitted certificate-validity guard. -/
def CertificateCodecTotal : Prop := ∀ code : Nat,
  ∃ lines : List GorbowProofChecker.Line,
    Encodable.encode lines=code ∧ GorbowNumericCertificate.decodeCertificate code=some lines

/-- All-vector original bound/initial/finish functions, including all decode and
default branches. Never reflected as an internal source equation. -/
def NativeAuxiliaries : Prop :=
  SixSol20261112.HistoryMachine.BoundProgram bound ∧ SixSol20261112.HistoryMachine.InitialProgram initial ∧ SixSol20261112.HistoryMachine.FinishProgram finalizer

def InternalBound : Prop := ∀ n (p : Program n) (tag : Nat),
  (nodes p)[tag]? = some ⟨1,bound⟩ → ∀ ctx (certificate : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (unaryCall tag certificate) certificate))

def InternalInitial : Prop := ∀ n (p : Program n) (tag ptag : Nat),
  (nodes p)[tag]? = some ⟨1,initial⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (certificate : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (unaryCall tag certificate) (HistoryKernel.pairCall ptag (.succ .zero) certificate)))

/-- Exact acceptance characterization on every actual nonempty successful
history image, with arbitrary raw entry, tails, requested formula and certificate.
No wellformedness or calibration premise is used internally. -/
def InternalFinishCharacterization : Prop := ∀ n (p : Program n) (ftag ptag ctag : Nat),
  (nodes p)[ftag]? = some ⟨4,finalizer⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  ∀ ctx (context raw tail lines requested formula certificate : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (finishCharacterization ftag ptag ctag context raw tail lines requested formula certificate))

/-- NONE and SOME empty remain rejection, even when entry code zero could be valid. -/
def InternalFinishFailure : Prop := ∀ n (p : Program n) (ftag ptag : Nat),
  (nodes p)[ftag]? = some ⟨4,finalizer⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (lines requested formula certificate : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (finishFailure ftag ptag lines requested formula certificate))

/-- Explicit NEW construction: bound/initial/finalizer above are fixed literal
ASTs before pF/pR/c/CK/producer are chosen. Prior tuples remain untouched.
Retains full kernel/append, source/CK/producer, fuel/fusion/iterator/drain clauses.
Existing history-independent dispatcher leaf witnesses are retained as leaves;
no claim that those leaf ASTs or the previous opaque auxiliaries are identical.
This is auxiliary closure, not full certificate constructor closure or HB2/HB3. -/
def SameSourceLiteralAuxiliaries : Prop :=
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
      Nonempty (Derivation (S pF pR q) (failureClause pF valid logical arithmetic axiomProgram))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Targets
