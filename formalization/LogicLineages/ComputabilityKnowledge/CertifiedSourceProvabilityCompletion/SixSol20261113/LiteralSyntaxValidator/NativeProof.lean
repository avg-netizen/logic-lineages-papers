module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open LiteralRawMP.NativeProof (pairEval)

theorem taskEval (context raw : Nat) :
 evaluate formulaTask (context ::ᵥ raw ::ᵥ nil) = Encodable.encode ((1,context) : GorbowSyntaxValidation.Task) := by
 simp only [formulaTask,twoEval,constantEval,projectionEval,get2_0,pairEval,encodeProd,encodeNat]

theorem tasksEval (context raw : Nat) :
 evaluate formulaTasks (context ::ᵥ raw ::ᵥ nil) = Encodable.encode [((1,context) : GorbowSyntaxValidation.Task)] := by
 simp only [formulaTasks,twoEval,taskEval,constantEval]
 change evaluate HistoryCodec.cons (Encodable.encode ((1,context) : GorbowSyntaxValidation.Task) ::ᵥ Encodable.encode ([] : List GorbowSyntaxValidation.Task) ::ᵥ nil) = _
 rw [HistoryCodec.NativeProof.nativeConsAllVectors]
 rfl

theorem formulaEncoded (context : Nat) (raw : List Nat) :
 evaluate formulaValidator (context ::ᵥ Encodable.encode raw ::ᵥ nil) =
 HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula context raw) := by
 simp only [formulaValidator,twoEval,formulaScan,tasksEval,projectionEval,get2_1,constantEval]
 rw [LiteralSyntaxScan.NativeProof.scanEncoded,equalEval]
 have he : (Encodable.encode (GorbowSyntaxValidation.scan [(1,context)] raw) = 1) ↔
   GorbowSyntaxValidation.scan [(1,context)] raw = some [] := by
  change (Encodable.encode (GorbowSyntaxValidation.scan [(1,context)] raw) =
   Encodable.encode (some ([] : List GorbowSyntaxValidation.Task))) ↔ _
  exact Encodable.encode_injective.eq_iff
 by_cases h : GorbowSyntaxValidation.scan [(1,context)] raw = some []
 · simp [he,GorbowSyntaxValidation.validFormula,HistoryDispatcher.truth,h]
 · simp [he,GorbowSyntaxValidation.validFormula,HistoryDispatcher.truth,h]

theorem nativeFormula : Targets.NativeFormula := by
 intro v
 obtain ⟨raw,hr⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (v.get 1)
 have hd : Encodable.decode (α := List Nat) (v.get 1) = some raw := by
  rw [← hr]; exact Encodable.encodek raw
 have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ nil := by
  ext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hd]
 simpa only [hr,Option.getD_some,← hv] using formulaEncoded (v.get 0) raw

theorem lineContextEncoded (line : GorbowProofChecker.Line) :
 evaluate lineContext (Encodable.encode line ::ᵥ nil) = GorbowProofChecker.context line := by
 rw [lineContext,HistoryDecoder.NativeProof.evaluateDecoder]
 change (Nat.unpair (Encodable.encode line)).1 = _
 rcases line with ⟨context,rest⟩
 rw [encodeProd,Nat.unpair_pair]
 rfl

theorem lineRawEncoded (line : GorbowProofChecker.Line) :
 evaluate lineRaw (Encodable.encode line ::ᵥ nil) = Encodable.encode (GorbowProofChecker.conclusion line) := by
 rw [lineRaw,oneEval,HistoryDecoder.NativeProof.evaluateDecoder,HistoryDecoder.NativeProof.evaluateDecoder]
 change (Nat.unpair (Nat.unpair (Encodable.encode line)).2).1 = _
 rcases line with ⟨context,raw,rest⟩
 rw [encodeProd,Nat.unpair_pair,encodeProd,Nat.unpair_pair]
 rfl

theorem lineEncoded (line : GorbowProofChecker.Line) :
 evaluate lineValidator (Encodable.encode line ::ᵥ nil) =
 HistoryDispatcher.truth (GorbowSyntaxValidation.validFormula
  (GorbowProofChecker.context line) (GorbowProofChecker.conclusion line)) := by
 rw [lineValidator,twoEval,lineContextEncoded,lineRawEncoded]
 exact formulaEncoded (GorbowProofChecker.context line) (GorbowProofChecker.conclusion line)

theorem nativeLine : Targets.NativeLine := by
 intro v
 obtain ⟨line,he⟩ := HistoryKernel.CodecTotalProof.lineTotal v.head
 have hd : HistoryDispatcher.decodedLine v.head = line := by
  rw [HistoryDispatcher.decodedLine,← he,Encodable.encodek,Option.getD_some]
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 change evaluate lineValidator v = HistoryDispatcher.truth
  (GorbowSyntaxValidation.validFormula (GorbowProofChecker.context (HistoryDispatcher.decodedLine v.head))
   (GorbowProofChecker.conclusion (HistoryDispatcher.decodedLine v.head)))
 rw [hd]
 simpa only [he,← hv] using lineEncoded line
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.NativeProof
