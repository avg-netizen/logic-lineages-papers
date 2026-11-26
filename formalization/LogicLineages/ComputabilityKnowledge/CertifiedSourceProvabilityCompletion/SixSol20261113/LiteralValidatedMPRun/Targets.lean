module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open LiteralRawMP HistoryRunSplice LiteralMPRun

/-- New MP line validity is a conclusion from actual successful-run provenance,
formula-boundary validity and literal implication-conclusion closure. -/
def InternalNewLineValidity : Prop := ∀ (l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher validity l a x⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
      (newLineValid dispatcherTag ltag ptag validity l a x context psi ant)))

/-- Fresh literal validity discharges the earlier new-line premise from the
two actual input runs. Trailing singleton executes from JOINED successful history.
No native calibration, validity assumption, or semantic formula-image premise. -/
def InternalTrailingStep : Prop := ∀ (l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher validity l a x⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
        (.equal (run itag ptag (.succ .zero)
          (.succ (joinedHistory atag ptag ctag context phi psi tailI tailA))
          (trailingLines ltag ptag ctag context psi ant) index fuel)
          (outputState atag ptag ctag context phi psi tailI tailA))))

/-- Actual constructor code is both certificate and encoded iteration bound.
No equality between encoded bound and true list length is assumed. -/
def InternalConstructedRun : Prop := ∀ (l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher validity l a x⟩ →
  ∀ mtag, (nodes p)[mtag]? = some ⟨4,constructor⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
        (.equal (run itag ptag (certificate mtag context psi imp ant) (.succ .zero)
          (certificate mtag context psi imp ant) index fuel)
          (outputState atag ptag ctag context phi psi tailI tailA))))

/-- Acceptance of the actually installed all-literal core from the two runs. This
explicitly includes its real bound/initializer/finalizer AST, but makes no SAME
source/root installation, unconditional validity, or HB completion claim. -/
def InternalCoreAcceptance : Prop := ∀ (l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher validity l a x⟩ →
  ∀ mtag qtag,
  (nodes p)[mtag]? = some ⟨4,constructor⟩ →
  (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker validity l a x
    LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
        (.equal (LiteralCheckerAcceptance.coreCall qtag index fuel context (.add psi psi)
          (certificate mtag context psi imp ant)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.Targets
