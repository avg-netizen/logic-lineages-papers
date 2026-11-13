module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector

/-- Arbitrary Option payload/count; actual nil stutter through iteration. -/
def InternalIdle : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag ptag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ → ∀ ctx (count option index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (run itag ptag count option .zero index fuel) (state ptag option .zero)))

/-- True-length exhaustion for arbitrary code and Option payload. -/
def InternalLengthDrain : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag ltag atag ptag ctag dtag droptag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ → ∀ ctx (code option index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (call dtag (run itag ptag (HistoryLengthOffset.lengthCall ltag code) option code index fuel ::ᵥ nil)) .zero))

/-- Encoded bound is NOT equated to true length. Actual runs have equal outputs
by exhaustion and idle stability, internally proved without native reflection. -/
def InternalBoundConversion : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag ltag atag ptag ctag dtag droptag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ → ∀ ctx (code option index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (run itag ptag code option code index fuel)
      (run itag ptag (HistoryLengthOffset.lengthCall ltag code) option code index fuel)))

/-- Successful prefix splicing at exact true length; arbitrary starting history. -/
def InternalPrefixSplice : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag ltag atag ptag ctag dtag droptag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ → ∀ ctx (left right history out index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (prefixSplice itag ltag atag ptag left right history out index fuel))

/-- Actual certificate concatenation at common index/fuel. Standalone length
installation explicit; no current SAME/root, trailing MP, or HB claim. -/
def InternalAppendRuns : Prop := ∀ (v l a : Program 1) (x : Program 3),
  ∀ n (p : Program n) (itag ltag atag ptag ctag dtag droptag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ → ∀ ctx (left right outLeft outRight index fuel : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (appendRuns itag atag ptag left right outLeft outRight index fuel))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.Targets
