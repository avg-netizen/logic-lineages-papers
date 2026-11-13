module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open LiteralValidatedMPRun LiteralRawMP LiteralMPRun LiteralCheckerAcceptance

/-- Core acceptance produces a genuine tail witness for the exact requested
raw code; no successful-run, decoding, semantic syntax or validity premise. -/
def InternalAcceptedRun : Prop := ∀ (l a : Program 1) (x : Program 3), ∀ n (p : Program n)
 (qtag itag ptag ctag dtag droptag : Nat),
 (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker validity l a x
   LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
 (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
 ∀ ctx (context raw certificate index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (coreCall qtag index fuel context (.add raw raw) certificate) (.succ .zero))
   (successfulRun itag ptag ctag context raw certificate index fuel)))

/-- Core-level literal MP preservation with the ORIGINAL canonical certificate
constructor, encoded bound and unchanged common runtime parameters. Two actual
core acceptances replace the stronger successful-run premises. No extra
new-line validity, syntactic boundary, list-image, native calibration or source
identity premise. Generic registry only; not a SAME published source/HB claim. -/
def InternalCoreMP : Prop := ∀ (l a : Program 1) (x : Program 3), ∀ n (p : Program n)
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
  ∀ ctx (context phi psi imp ant index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputAcceptance qtag atag ctag context phi psi imp ant index fuel)
        (.equal (LiteralCheckerAcceptance.coreCall qtag index fuel context (.add psi psi)
          (certificate mtag context psi imp ant)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.Targets
