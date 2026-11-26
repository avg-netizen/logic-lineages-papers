module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeCalls
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof

theorem exactNative : Targets.Native := by
 intro n p q tag offset value hoffset
 have hleft := NativeCalls.left tag offset value
 have hmid := NativeCalls.middle tag offset value
 have hright := NativeCalls.first tag offset value
 have hs := NativeRoot.rootSeedEval tag offset value
 have hp := NativeCalls.projectionSeedEval tag offset value
 have hc : NativeCalls.calls tag offset value = List.Vector.ofFn (fun i : Fin 2 =>
  call (tag + argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) i) (NativeCalls.nums value)) := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Fin.eq_zero j
    subst j
    simp only [NativeCalls.calls,List.Vector.get_cons_succ,List.Vector.get_cons_zero,List.Vector.get_ofFn,hoffset]
 have hr := SyntaxProof.actualRoot p q tag offset hoffset
 unfold program
 rw [CurrentRecursionBaseProgram.TransitivityNativeProof.transitivityEval _ _ _ _ _ _ _ _ _ hleft hmid hright,hs,hp]
 rw [hr]
 change transitivityNumber (call tag (NativeCalls.nums value)) (call (tag+1) (NativeCalls.calls tag offset value))
  ((NativeCalls.calls tag offset value).get 0) _ _ = _
 rw [hc]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeProof
