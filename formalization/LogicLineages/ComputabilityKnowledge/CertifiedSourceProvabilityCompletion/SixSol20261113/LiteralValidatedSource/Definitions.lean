module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameStatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries HistoryRuleSuffix
/-- Fixed BEFORE all remaining leaf and source witnesses. Not an identity with
any earlier existential validity leaf or source tuple. -/
def valid : Program 1 := LiteralSyntaxValidator.lineValidator
/-- Exact entire retained old conjunction, including its final dropOffset
existential. Only the formerly existential validity leaf is now fixed above. -/
def Retained (logical arithmetic : Program 1) (axiomProgram : Program 3)
 (appendOffset : Nat) (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
 (tagG : Nat) (pG : Program 6) : Prop :=
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


def iteratorTag (pF : Program 1) (l a : Program 1) (x : Program 3) : Nat :=
 SixSol20261112.HistoryMachine.iteratorTag (GorbowNamedInternalProvability.checkerTag pF)
  (HistoryKernel.kernel valid l a x) bound initial finalizer
def validityTag (pF : Program 1) (l a : Program 1) (x : Program 3) : Nat :=
 HistoryTopProvenance.validityTag (iteratorTag pF l a x) valid l a x
def formulaTag (vtag : Nat) : Nat := vtag + 1
def lineArguments : Fin 2 → Program 1 := Fin.cases LiteralSyntaxValidator.lineContext
 (Fin.cases LiteralSyntaxValidator.lineRaw Fin.elim0)
def leftTag (vtag : Nat) : Nat :=
 vtag + argumentTag LiteralSyntaxValidator.formulaValidator lineArguments 0
def lineRawTag (vtag : Nat) : Nat :=
 vtag + argumentTag LiteralSyntaxValidator.formulaValidator lineArguments 1
def rightTag (vtag : Nat) : Nat :=
 lineRawTag vtag + argumentTag (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => HistoryDecoder.decoder true) 0

def formulaArguments : Fin 2 → Program 2 := Fin.cases LiteralSyntaxValidator.formulaScan
 (Fin.cases (constant 2 1) Fin.elim0)
def scanWrapper (vtag : Nat) : Nat :=
 formulaTag vtag + argumentTag equalCode formulaArguments 0
def scanTag (vtag : Nat) : Nat := scanWrapper vtag + 1
def equalityTag (vtag : Nat) : Nat := formulaTag vtag + 1
def scanArguments : Fin 2 → Program 2 := Fin.cases LiteralSyntaxValidator.formulaTasks
 (Fin.cases (.projection 1) Fin.elim0)
def taskListWrapper (vtag : Nat) : Nat :=
 scanWrapper vtag + argumentTag LiteralSyntaxScan.scanCode scanArguments 0
def taskConsTag (vtag : Nat) : Nat := taskListWrapper vtag + 1
def taskArguments : Fin 2 → Program 2 := Fin.cases LiteralSyntaxValidator.formulaTask
 (Fin.cases (constant 2 0) Fin.elim0)
def taskPairTag (vtag : Nat) : Nat :=
 taskListWrapper vtag + argumentTag HistoryCodec.cons taskArguments 0 + 1

def booleanClause (ftag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.disj (.equal (LiteralSyntaxValidator.formulaCall ftag (.var (0 : Fin 2)) (.var 1)) .zero)
   (.equal (LiteralSyntaxValidator.formulaCall ftag (.var (0 : Fin 2)) (.var 1)) (.succ .zero)))
def lineClause (vtag ftag ptag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.equal (LiteralSyntaxValidator.lineCall vtag
   (HistoryKernel.pairCall ptag (.var (0 : Fin 3)) (HistoryKernel.pairCall ptag (.var 1) (.var 2))))
   (LiteralSyntaxValidator.formulaCall ftag (.var 0) (.var 1)))
def implicationClause (ftag atag ctag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (.equal (LiteralSyntaxValidator.formulaCall ftag (.var (0 : Fin 3)) (.var 1)) (.succ .zero))
   (.imp (.equal (LiteralSyntaxValidator.formulaCall ftag (.var 0)
    (LiteralSyntaxValidator.binaryRaw atag ctag 7 (.var 1) (.var 2))) (.succ .zero))
    (.equal (LiteralSyntaxValidator.formulaCall ftag (.var 0) (.var 2)) (.succ .zero))))
def quantifierClause (ftag ctag token : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.equal (LiteralSyntaxValidator.formulaCall ftag (.var (0 : Fin 2))
   (LiteralSyntaxValidator.quantifiedRaw ctag token (.var 1)))
   (LiteralSyntaxValidator.formulaCall ftag (.succ (.var 0)) (.var 1)))
def scanFusionClause (stag atag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (.equal (LiteralSyntaxScan.scanCall stag (.var (0 : Fin 4)) (.var 1)) (.succ (.var 3)))
   (.equal (LiteralSyntaxScan.scanCall stag (.var 0) (HistoryAppend.appendCall atag (.var 1) (.var 2)))
    (LiteralSyntaxScan.scanCall stag (.var 3) (.var 2))))
def scanFrameClause (stag atag : Nat) : Sentence :=
 GorbowStandardInduction.universalClosure
  (.imp (.equal (LiteralSyntaxScan.scanCall stag (.var (0 : Fin 4)) (.var 1)) (.succ (.var 2)))
   (.equal (LiteralSyntaxScan.scanCall stag (HistoryAppend.appendCall atag (.var 0) (.var 3)) (.var 1))
    (.succ (HistoryAppend.appendCall atag (.var 2) (.var 3)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource
