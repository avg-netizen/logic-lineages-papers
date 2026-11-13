module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open LiteralRawMP.NativeProof (pairEval appendLists)

theorem whenEqualEval (x yes no : Program 2) (k : Nat) (v : List.Vector Nat 2) :
 evaluate (whenEqual x k yes no) v = if evaluate x v = k then evaluate yes v else evaluate no v := by
 simp only [whenEqual,chooseEval,twoEval,equalEval,constantEval]
 split <;> simp_all

theorem consEval (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
 HistoryCodec.NativeProof.nativeConsAllVectors _
theorem successEval (a : Program 2) (v : List.Vector Nat 2) : evaluate (success a) v = (evaluate a v).succ := rfl

theorem expandAt (k n token : Nat) :
 evaluate expandCode (Nat.pair k n ::ᵥ token ::ᵥ nil) = Encodable.encode (GorbowSyntaxValidation.expand (k,n) token) := by
 simp only [expandCode,termBranch,formulaBranch,indexBranch,whenEqualEval,kind,context,task,singleton,double,
   successEval,oneEval,twoEval,projectionEval,constantEval,get2_0,get2_1,
   HistoryDecoder.NativeProof.evaluateDecoder,Nat.unpair_pair,HistoryDecoder.coordinate,
   pairEval,consEval,HistoryCodec.NativeProof.evaluateDifference]
 simp only [GorbowSyntaxValidation.expand]
 split_ifs <;> simp_all [encodeProd,encodeNat,HistoryLookup.NativeProof.encodeCons]

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
       simp only [hx]
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
