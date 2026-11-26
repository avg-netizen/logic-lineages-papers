module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open LiteralRawMP HistoryRunSplice

/-- The trailing singleton executes from the JOINED successful history, never
from empty history. Common index/fuel are unchanged. -/
def InternalTrailingStep : Prop := ∀ (v l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
      (.imp (newLineValid dispatcherTag ltag ptag v l a x context psi ant)
        (.equal (run itag ptag (.succ .zero)
          (.succ (joinedHistory atag ptag ctag context phi psi tailI tailA))
          (trailingLines ltag ptag ctag context psi ant) index fuel)
          (outputState atag ptag ctag context phi psi tailI tailA)))))

/-- Actual constructor code is both certificate and encoded iteration bound.
No equality between encoded bound and true list length is assumed. -/
def InternalConstructedRun : Prop := ∀ (v l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ →
  ∀ mtag, (nodes p)[mtag]? = some ⟨4,constructor⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
      (.imp (newLineValid dispatcherTag ltag ptag v l a x context psi ant)
        (.equal (run itag ptag (certificate mtag context psi imp ant) (.succ .zero)
          (certificate mtag context psi imp ant) index fuel)
          (outputState atag ptag ctag context phi psi tailI tailA)))))

/-- Conditional acceptance of the actually installed all-literal core. This
explicitly includes its real bound/initializer/finalizer AST, but makes no SAME
source/root installation, unconditional validity, or HB completion claim. -/
def InternalCoreAcceptance : Prop := ∀ (v l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ →
  ∀ mtag qtag,
  (nodes p)[mtag]? = some ⟨4,constructor⟩ →
  (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker v l a x
    LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
      (.imp (newLineValid dispatcherTag ltag ptag v l a x context psi ant)
        (.equal (LiteralCheckerAcceptance.coreCall qtag index fuel context (.add psi psi)
          (certificate mtag context psi imp ant)) (.succ .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.Targets
