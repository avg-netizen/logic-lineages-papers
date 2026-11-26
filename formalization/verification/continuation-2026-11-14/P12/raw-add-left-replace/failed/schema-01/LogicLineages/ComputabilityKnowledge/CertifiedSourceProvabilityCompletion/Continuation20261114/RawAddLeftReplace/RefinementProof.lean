module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.RefinementProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof TwoSol20261113.ReflexivityRecognizer
open NativeProof

theorem candidateSound (candidate original : Nat)
 (h : evaluate candidateTest (candidate ::ᵥ original ::ᵥ nil) ≠ 0) :
 HistoryDispatcher.logicalFunction (original ::ᵥ nil) = 1 := by
 let v := original ::ᵥ nil
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate leftTermCode v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate rightTermCode v)
 obtain ⟨c,hc⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal candidate
 let args := candidate ::ᵥ original ::ᵥ nil
 let aP := applyOne leftTermCode (.projection (1 : Fin 2))
 let bP := applyOne rightTermCode (.projection (1 : Fin 2))
 have hA : evaluate aP args = Encodable.encode a := ha.symm
 have hB : evaluate bP args = Encodable.encode b := hb.symm
 have hC : evaluate (.projection (0 : Fin 2)) args = Encodable.encode c := hc.symm
 have hl := NativeProof.lineEval aP bP (.projection 0) args a b c hA hB hC
 have hta : evaluate (applyOne termValidator aP) args = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 a) := by
  rw [oneEval,hA,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 have htb : evaluate (applyOne termValidator bP) args = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 b) := by
  rw [oneEval,hB,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 have htc : evaluate (applyOne termValidator (.projection (0 : Fin 2))) args = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 c) := by
  rw [oneEval,hC,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 change evaluate (conjunction (applyTwo equalCode (.projection 1) (line aP bP (.projection 0)))
  (conjunction (applyOne termValidator aP) (conjunction (applyOne termValidator bP)
   (applyOne termValidator (.projection 0))))) args ≠ 0 at h
 simp only [conjunctionEval,twoEval,projectionEval,get2_1,hl,equalEval,hta,htb,htc] at h
 have hget : args.get (1 : Fin 2) = original := rfl
 rw [hget] at h
 by_cases he : original = Encodable.encode (nativeLine a b c)
 · by_cases hva : GorbowSyntaxValidation.validTerm 0 a = true
   · by_cases hvb : GorbowSyntaxValidation.validTerm 0 b = true
     · by_cases hvc : GorbowSyntaxValidation.validTerm 0 c = true
       · rw [he]; exact NativeProof.rawLineAccepted a b c hva hvb hvc
       · simp [he,hva,hvb,hvc,HistoryDispatcher.truth] at h
     · simp [he,hva,hvb,HistoryDispatcher.truth] at h
   · simp [he,hva,HistoryDispatcher.truth] at h
 · simp [he] at h

theorem compositionEval {n k : Nat} (f : Program k) (g : Fin k → Program n) (v : List.Vector Nat n) :
 evaluate (.composition f g) v = evaluate f (List.Vector.ofFn fun i => evaluate (g i) v) := rfl
theorem successorEval {n : Nat} (a : Program n) (v : List.Vector Nat n) :
 evaluate (.composition .succ (fun _ => a)) v = (evaluate a v).succ := rfl
theorem recognizerEval (v : List.Vector Nat 1) :
 evaluate recognizer v = evaluate (RawNumericSearch.search candidateTest) (v.head.succ ::ᵥ v.head ::ᵥ nil) := by
 rw [recognizer,compositionEval]
 apply congrArg (evaluate (RawNumericSearch.search candidateTest))
 apply List.Vector.ext
 intro i
 cases i using Fin.cases with
 | zero => simp only [List.Vector.get_ofFn,searchArguments,Fin.cases_zero,successorEval,projectionEval,List.Vector.get_cons_zero,List.Vector.get_zero]
 | succ i => cases i using Fin.cases with
   | zero => simp only [List.Vector.get_ofFn,searchArguments,Fin.cases_succ,Fin.cases_zero,projectionEval,List.Vector.get_cons_succ,List.Vector.get_cons_zero,List.Vector.get_zero,List.Vector.head_cons]
   | succ i => exact Fin.elim0 i

theorem nativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have hr := recognizerEval v
 rw [logicalLeaf,chooseEval]
 by_cases hz : evaluate recognizer v = 0
 · simp only [hz,if_true]; exact hold v
 · have hh := RawNumericSearch.StatementChecks.exactNative candidateTest v.head.succ v.head
   have hone : evaluate (RawNumericSearch.search candidateTest) (v.head.succ ::ᵥ v.head ::ᵥ nil)=1 := hh.1.resolve_left (by simpa only [← hr] using hz)
   obtain ⟨i,hi,hit⟩ := hh.2.mp hone
   have hf := candidateSound i v.head hit
   simp only [hz,if_false,constantEval]
   rw [hv]
   exact hf.symm
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.RefinementProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.RefinementProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.RefinementProof.candidateSound
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.RefinementProof.nativeRefinement
