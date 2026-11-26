module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.CodecProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof

theorem certificateCodecTotal : Targets.CertificateCodecTotal := by
  intro code
  obtain ⟨lines,he⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.lineTotal code
  refine ⟨lines,he,?_⟩
  rw [← he]
  simp [GorbowNumericCertificate.decodeCertificate]

theorem decodedLinesEncode (code : Nat) :
    Encodable.encode (SixSol20261112.HistoryMachine.decodedLines code)=code := by
  obtain ⟨lines,he,hd⟩ := certificateCodecTotal code
  simp only [SixSol20261112.HistoryMachine.decodedLines,hd,Option.getD_some,he]

theorem formulaDecodeExact (formula : Nat) (raw : List Nat) :
    GorbowSortedSyntaxCode.decodeFormulaRaw formula=some raw ↔
      formula=Encodable.encode raw+Encodable.encode raw := by
  simpa only [GorbowSortedSyntaxCode.formulaRawNumber,GorbowSortedSyntaxCode.tagFormula,
    GorbowCodeConstructors.number,two_mul] using
      GorbowSortedSyntaxCodeProof.exactRawDecoding.1 formula raw

theorem nativeBound : SixSol20261112.HistoryMachine.BoundProgram bound := by
  intro v
  change v.get 0 = Encodable.encode (SixSol20261112.HistoryMachine.decodedLines v.head)
  rw [decodedLinesEncode]
  rw [List.Vector.get_zero]

theorem nativeInitial : SixSol20261112.HistoryMachine.InitialProgram initial := by
  intro v
  rw [initial,twoEval,constantEval,projectionEval,HistoryCodec.NativeProof.nativePair]
  change Nat.pair 1 (v.get 0) = Nat.pair 1 (Encodable.encode (SixSol20261112.HistoryMachine.decodedLines v.head))
  rw [decodedLinesEncode]
  rw [List.Vector.get_zero]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.CodecProof
