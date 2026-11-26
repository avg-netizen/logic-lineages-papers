module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open HistoryRunSplice HistoryLengthOffset

def NativeRaw : Prop :=
  (∀ v : List.Vector Nat 3, evaluate lineProgram v = Encodable.encode
    (GorbowProofChecker.mpLine (v.get 0) ((GorbowNumericCertificate.decodeFormula (v.get 1)).getD []) (v.get 2) 0)) ∧
  (∀ v : List.Vector Nat 4, evaluate constructor v = GorbowNumericCertificate.certificateNumber
    (GorbowTheoryCertificateOperations.mpLines (v.get 0) ((GorbowNumericCertificate.decodeFormula (v.get 1)).getD [])
      ((GorbowNumericCertificate.decodeCertificate (v.get 2)).getD [])
      ((GorbowNumericCertificate.decodeCertificate (v.get 3)).getD [])))
/-- Only canonical even sorted formula codes are identified with the original
numeric mpCertificate. No odd-formula/default reflection is asserted. -/
def NativeEven : Prop := ∀ context (raw : List Nat) imp ant,
  evaluate constructor (context ::ᵥ Encodable.encode raw ::ᵥ imp ::ᵥ ant ::ᵥ nil) =
    GorbowTheoryCertificateOperations.mpCertificate context
      (GorbowSortedSyntaxCode.formulaRawNumber raw) imp ant

def ActualChildren : Prop := ∃ lengthOffset lineOffset : Nat,
  (nodes constructor)[lengthOffset]? = some ⟨1,lengthProgram⟩ ∧
  (nodes constructor)[lineOffset]? = some ⟨3,lineProgram⟩

def InternalConstructor : Prop := ∀ n (p : Program n) (tag ltag atag ptag ctag : Nat),
  (nodes p)[tag]? = some ⟨4,constructor⟩ →
  (nodes p)[ltag]? = some ⟨1,lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ → ∀ ctx (context raw imp ant : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call tag (context ::ᵥ raw ::ᵥ imp ::ᵥ ant ::ᵥ nil))
      (HistoryAppend.appendCall atag (HistoryAppend.appendCall atag imp ant)
        (HistoryLookup.consCall ctag (lineValue ptag context raw (lengthCall ltag ant)) .zero))))

/-- References are conclusions, derived from actual successful input runs;
no reference-success or history-length equality is assumed. -/
def InternalReferences : Prop := ∀ (v l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
      (references ltag atag ptag ctag rtag context phi psi ant tailI tailA)))

/-- Bounded endpoint: actual full dispatcher acceptance with its new-line
validity gate EXPLICITLY retained. No HB or unconditional validity claim. -/
def InternalDispatcher : Prop := ∀ (v l a : Program 1) (x : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  ∀ dispatcherTag,
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ →
  ∀ ctx (context phi psi imp ant tailI tailA index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel)
      (.imp (.equal (call (validityTag dispatcherTag v l a x)
          (lineValue ptag context psi (lengthCall ltag ant) ::ᵥ nil)) (.succ .zero))
        (.equal (HistoryDispatcher.dispatcherCall dispatcherTag index fuel
          (joinedHistory atag ptag ctag context phi psi tailI tailA)
          (lineValue ptag context psi (lengthCall ltag ant))) (.succ .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Targets
