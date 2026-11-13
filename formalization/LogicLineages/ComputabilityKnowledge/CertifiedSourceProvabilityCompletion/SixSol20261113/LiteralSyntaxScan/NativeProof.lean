module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeTickProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof NativeTickProof
open LiteralRawMP.NativeProof (pairEval)

theorem scanEncoded (tasks : List GorbowSyntaxValidation.Task) (raw : List Nat) :
 evaluate scanCode (Encodable.encode tasks ::ᵥ Encodable.encode raw ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.scan tasks raw) := by
 have hi : evaluate initial (Encodable.encode tasks ::ᵥ Encodable.encode raw ::ᵥ nil) =
   Nat.pair (Encodable.encode raw) (Encodable.encode (some tasks)) := by
   change evaluate HistoryCodec.pair (Encodable.encode raw ::ᵥ (Encodable.encode tasks).succ ::ᵥ nil) = _
   exact pairEval _ _
 simp only [scanCode,oneEval,finalState,twoEval,projectionEval,get2_1,HistoryLengthOffset.NativeProof.lengthList,hi]
 rw [iteratorRaw,HistoryDecoder.NativeProof.evaluateDecoder,Nat.unpair_pair]
 rfl

theorem nativeScan : Targets.NativeScan := by
 intro v
 obtain ⟨tasks,ht⟩ := HistoryKernel.CodecTotalProof.listTotal
   (HistoryKernel.CodecTotalProof.prodTotal HistoryKernel.CodecTotalProof.natTotal HistoryKernel.CodecTotalProof.natTotal) (v.get 0)
 obtain ⟨raw,hr⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (v.get 1)
 have hdt : Encodable.decode (α := List GorbowSyntaxValidation.Task) (v.get 0) = some tasks := by
   rw [← ht]; exact Encodable.encodek tasks
 have hdr : Encodable.decode (α := List Nat) (v.get 1) = some raw := by
   rw [← hr]; exact Encodable.encodek raw
 have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ nil := by
   ext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hdt,hdr]
 simpa only [ht,hr,Option.getD_some,← hv] using scanEncoded tasks raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NativeProof
