module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeTermProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeFormulaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof HistoryLengthOffset
open LiteralRawMP.NativeProof (appendLists)
open NativeAtomsProof

theorem expandAt (k n token : Nat) :
 evaluate expandCode (Nat.pair k n ::ᵥ token ::ᵥ nil) = Encodable.encode (GorbowSyntaxValidation.expand (k,n) token) := by
 rw [expandCode,whenEqualEval,kindAt]
 by_cases h0 : k=0
 · subst k
   simpa only [if_pos rfl] using NativeTermProof.branchAt n token
 · rw [if_neg h0,whenEqualEval,kindAt]
   by_cases h1 : k=1
   · subst k
     simpa only [if_pos rfl] using NativeFormulaProof.branchAt n token
   · rw [if_neg h1,whenEqualEval,kindAt]
     by_cases h2 : k=2
     · subst k
       rw [if_pos rfl]
       simp only [indexBranch,chooseEval,twoEval,projectionEval,get2_1,contextAt,HistoryCodec.NativeProof.evaluateDifference,constantEval]
       simp only [GorbowSyntaxValidation.expand]
       by_cases ht : token<n
       · have hn : n-token ≠ 0 := by omega
         simp [ht,hn]
       · have hn : n-token = 0 := by omega
         simp [ht,hn]
     · rw [if_neg h2,constantEval]
       simp [GorbowSyntaxValidation.expand,h0,h1,h2]

theorem nativeExpand : Targets.NativeExpand := by
 intro v
 have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ nil := by
   ext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have h := expandAt (Nat.unpair (v.get 0)).1 (Nat.unpair (v.get 0)).2 (v.get 1)
 rw [Nat.pair_unpair] at h
 calc
   evaluate expandCode v = evaluate expandCode (v.get 0 ::ᵥ v.get 1 ::ᵥ nil) := congrArg (evaluate expandCode) hv
   _ = _ := h

theorem stepAt (s : GorbowSyntaxValidation.State) (token : Nat) :
 evaluate stepCode (Encodable.encode s ::ᵥ token ::ᵥ nil) = Encodable.encode (GorbowSyntaxValidation.step s token) := by
 cases s with
 | none => simp only [stepCode,chooseEval,constantEval,projectionEval,get2_0]; rfl
 | some tasks =>
   cases tasks with
   | nil =>
     simp only [stepCode,chooseEval,constantEval,projectionEval,get2_0,stack,oneEval,HistoryCodec.NativeProof.evaluatePredecessor]
     rfl
   | cons t rest =>
     have he : evaluate expanded (Encodable.encode (some (t::rest)) ::ᵥ token ::ᵥ nil) =
       Encodable.encode (GorbowSyntaxValidation.expand t token) := by
       simp only [expanded,twoEval,headTask,oneEval,stack,projectionEval,get2_0,get2_1,
         HistoryCodec.NativeProof.evaluatePredecessor]
       change evaluate expandCode (evaluate HistoryLookup.head (Encodable.encode (t::rest) ::ᵥ nil) ::ᵥ token ::ᵥ nil) = _
       rw [HistoryLookup.NativeProof.headCons]
       exact expandAt t.1 t.2 token
     have ht : evaluate restTasks (Encodable.encode (some (t::rest)) ::ᵥ token ::ᵥ nil) = Encodable.encode rest := by
       simp only [restTasks,oneEval,stack,projectionEval,get2_0,HistoryCodec.NativeProof.evaluatePredecessor]
       exact HistoryLookup.NativeProof.tailList (t::rest)
     have hs : evaluate stack (Encodable.encode (some (t::rest)) ::ᵥ token ::ᵥ nil) = Encodable.encode (t::rest) := by
       simp only [stack,oneEval,projectionEval,get2_0,HistoryCodec.NativeProof.evaluatePredecessor]
       rfl
     simp only [stepCode,chooseEval,projectionEval,get2_0,constantEval,hs,he,successEval,appended,twoEval,
       oneEval,HistoryCodec.NativeProof.evaluatePredecessor,ht]
     cases hx : GorbowSyntaxValidation.expand t token with
     | none => simp [GorbowSyntaxValidation.step,hx,HistoryLookup.NativeProof.encodeCons]
     | some added =>
       change (if Encodable.encode (some (t::rest))=0 then 0 else
         if Encodable.encode (t::rest)=0 then 0 else
         if Encodable.encode (some added)=0 then 0 else
         (evaluate HistoryAppend.append (Encodable.encode added ::ᵥ Encodable.encode rest ::ᵥ nil)).succ) = _
       rw [appendLists]
       simp [GorbowSyntaxValidation.step,hx,HistoryLookup.NativeProof.encodeCons]

theorem nativeStep : Targets.NativeStep := by
 intro v
 obtain ⟨s,he⟩ := HistoryKernel.CodecTotalProof.optionTotal
   (HistoryKernel.CodecTotalProof.listTotal
     (HistoryKernel.CodecTotalProof.prodTotal HistoryKernel.CodecTotalProof.natTotal HistoryKernel.CodecTotalProof.natTotal)) (v.get 0)
 have hd : Encodable.decode (α := GorbowSyntaxValidation.State) (v.get 0) = some s := by
   rw [← he]; exact Encodable.encodek s
 have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ nil := by
   ext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hd]
 simpa only [he,Option.getD_some,← hv] using stepAt s (v.get 1)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeProof
