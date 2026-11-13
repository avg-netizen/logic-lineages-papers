module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.NativeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof HistoryLengthOffset

theorem appendLists {α : Type} [Encodable α] (left right : List α) :
 evaluate HistoryAppend.append (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) = Encodable.encode (left ++ right) := by
 rw [HistoryAppend.NativeProof.appendEval]
 induction left with
 | nil => rfl
 | cons a left ih =>
   rw [HistoryLookup.NativeProof.encodeCons,HistoryAppend.NativeProof.resultCons,ih]
   rfl

theorem formulaCodecTotal (code : Nat) : ∃ raw : List Nat,
 Encodable.encode raw=code ∧ GorbowNumericCertificate.decodeFormula code=some raw := by
 obtain ⟨raw,he⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal code
 refine ⟨raw,he,?_⟩
 rw [← he]
 simp [GorbowNumericCertificate.decodeFormula]

theorem lineEncoded (context ref1 : Nat) (raw : List Nat) :
 evaluate lineProgram (context ::ᵥ Encodable.encode raw ::ᵥ ref1 ::ᵥ nil) =
 Encodable.encode (GorbowProofChecker.mpLine context raw ref1 0) := by
 simp only [lineProgram,twoEval,constantEval,projectionEval,HistoryCodec.NativeProof.nativePair]
 rfl

theorem constructorEncoded (context : Nat) (raw : List Nat) (imp ant : List GorbowProofChecker.Line) :
 evaluate constructor (context ::ᵥ Encodable.encode raw ::ᵥ Encodable.encode imp ::ᵥ Encodable.encode ant ::ᵥ nil) =
 Encodable.encode (GorbowTheoryCertificateOperations.mpLines context raw imp ant) := by
 have hline : evaluate newLine (context ::ᵥ Encodable.encode raw ::ᵥ Encodable.encode imp ::ᵥ Encodable.encode ant ::ᵥ nil) =
   Encodable.encode (GorbowProofChecker.mpLine context raw ant.length 0) := by
   change evaluate lineProgram (context ::ᵥ Encodable.encode raw ::ᵥ evaluate lengthProgram (Encodable.encode ant ::ᵥ nil) ::ᵥ nil) = _
   rw [HistoryLengthOffset.NativeProof.lengthList,lineEncoded]
 change evaluate HistoryAppend.append
   (evaluate HistoryAppend.append (Encodable.encode imp ::ᵥ Encodable.encode ant ::ᵥ nil) ::ᵥ
     evaluate HistoryCodec.cons (evaluate newLine (context ::ᵥ Encodable.encode raw ::ᵥ Encodable.encode imp ::ᵥ Encodable.encode ant ::ᵥ nil) ::ᵥ 0 ::ᵥ nil) ::ᵥ nil) = _
 rw [appendLists,hline,HistoryCodec.NativeProof.nativeConsAllVectors]
 change evaluate HistoryAppend.append (Encodable.encode (imp ++ ant) ::ᵥ Encodable.encode [GorbowProofChecker.mpLine context raw ant.length 0] ::ᵥ nil) = _
 exact appendLists _ _

theorem nativeRaw : Targets.NativeRaw := by
 constructor
 · intro v
   obtain ⟨raw,he,hd⟩ := formulaCodecTotal (v.get 1)
   have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ v.get 2 ::ᵥ nil := by ext i; fin_cases i <;> rfl
   rw [hv]
   change evaluate lineProgram (v.get 0 ::ᵥ v.get 1 ::ᵥ v.get 2 ::ᵥ nil) = _
   rw [hd]
   simpa only [he,Option.getD_some] using lineEncoded (v.get 0) (v.get 2) raw
 · intro v
   obtain ⟨raw,hr,hdr⟩ := formulaCodecTotal (v.get 1)
   obtain ⟨imp,hi,hdi⟩ := LiteralCheckerAuxiliaries.CodecProof.certificateCodecTotal (v.get 2)
   obtain ⟨ant,ha,hda⟩ := LiteralCheckerAuxiliaries.CodecProof.certificateCodecTotal (v.get 3)
   have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ v.get 2 ::ᵥ v.get 3 ::ᵥ nil := by ext i; fin_cases i <;> rfl
   rw [hv]
   change evaluate constructor (v.get 0 ::ᵥ v.get 1 ::ᵥ v.get 2 ::ᵥ v.get 3 ::ᵥ nil) = _
   rw [hdr,hdi,hda]
   simpa only [hr,hi,ha,Option.getD_some,GorbowNumericCertificate.certificateNumber] using constructorEncoded (v.get 0) raw imp ant

theorem nativeEven : Targets.NativeEven := by
 intro context raw imp ant
 have hr := nativeRaw.2 (context ::ᵥ Encodable.encode raw ::ᵥ imp ::ᵥ ant ::ᵥ nil)
 have hd : GorbowNumericCertificate.decodeFormula (Encodable.encode raw)=some raw := by simp [GorbowNumericCertificate.decodeFormula]
 have he := (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 (GorbowSortedSyntaxCode.formulaRawNumber raw) raw).mpr rfl
 simpa only [get4_0,get4_1,get4_2,get4_3,hd,Option.getD_some,GorbowTheoryCertificateOperations.mpCertificate,he] using hr
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.NativeProof
