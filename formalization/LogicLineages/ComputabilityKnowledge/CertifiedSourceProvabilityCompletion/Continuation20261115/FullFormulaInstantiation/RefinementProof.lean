module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.RefinementProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof
open TwoSol20261113.ReflexivityRecognizer TwoSol20261113.ReflexivityRecognizer.NativeProof

theorem nativeRefinement : Targets.NativeRefinement := by
 intro f old hold v
 obtain ⟨raw,hr⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate argumentCode v)
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have ht : evaluate (applyOne termValidator argumentCode) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 raw) := by
  rw [oneEval,← hr,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 by_cases hvalid : GorbowSyntaxValidation.validTerm 0 raw = true
 · have hg : GorbowLogicalAxiomCode.guardTerms 0 1 [raw] = true := by
    simp [GorbowLogicalAxiomCode.guardTerms,hvalid]
   have hall := (GorbowLogicalAxiomCodeProof.guardCalibration.2 0 1 [raw]).mp hg
   obtain ⟨u,hu⟩ := hall.2 raw (by simp)
   subst raw
   have hl : evaluate (applyOne (FullFormulaInstantiation.line f) argumentCode) v =
    Encodable.encode (FullFormulaInstantiation.nativeLine f u) := by
    rw [oneEval,← hr]
    exact NativeProof.nativeLine f u
   simp only [logicalLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
    hl,equalEval,ht,constantEval,List.Vector.get_zero]
   by_cases he : v.head = Encodable.encode (FullFormulaInstantiation.nativeLine f u)
   · have hf : HistoryDispatcher.logicalFunction v = 1 := by
      rw [hv,he]
      exact NativeProof.nativeAcceptance f u
     simp [he,hvalid,HistoryDispatcher.truth,hf]
   · simp [he,hold]
 · simp only [logicalLeaf,chooseEval,recognizer,conjunctionEval,ht,HistoryDispatcher.truth,hvalid,ite_false,constantEval]
   simp [hold]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.RefinementProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.RefinementProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.RefinementProof.nativeRefinement
