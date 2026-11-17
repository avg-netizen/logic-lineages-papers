module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.ProjectionGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TransitivityGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem exactGraph : Targets.Graph := by
 intro arity root K H pairTag rule13Tag hp h13 n p q tag offset producerTag hoffset hproducer ctx value
 let av := GraphCalls.nums K value
 let bv := GraphCalls.calls K tag offset value
 let rf := SyntaxProof.rootAt tag offset
 let rootCert := PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag rf av
 let projCert := PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag
  (CorrectedAugmentationErasure.projectionFormula tag) bv
 have hr : Computes root rootSeed (GraphValues.args tag offset value) rootCert := by
  intro addr ht
  obtain ⟨hg⟩ := RootGraph.rootGraph root K H pairTag rule13Tag hp h13 tag offset value addr ht
  obtain ⟨he⟩ := RootCode.rootCode root K H pairTag rule13Tag hp h13 tag offset value
  exact ⟨Logic.trans _ _ _ hg he⟩
 have hproj := ProjectionGraph.projectionGraph root K H pairTag rule13Tag hp h13 tag offset value
 have hg := CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph root (GraphValues.args tag offset value) K H
  leftCode middleCode firstCall rootSeed projectionSeed _ _ _ rootCert projCert
  (GraphCalls.left root K H tag offset value) (GraphCalls.middle root K H tag offset value)
  (GraphCalls.first root K H tag offset value) hr hproj
 have hc : bv = CorrectedAugmentationErasure.children K p q tag value := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : j = 0 := Fin.eq_zero j
    subst j
    simp only [bv,GraphCalls.calls,CorrectedAugmentationErasure.children,CurrentCompositionCertificate.childValues,
     List.Vector.get_ofFn,List.Vector.get_cons_succ,List.Vector.get_cons_zero,hoffset]
    rfl
 have hf := SyntaxProof.actualRoot p q tag offset hoffset
 have h := hg producerTag hproducer
 change Nonempty (Derivation (GorbowPRNumeralCalculation.Theory root)
  (.equal (call producerTag (GraphValues.args tag offset value))
   (transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
    (callValue K (Term.numeral tag) av) (callValue K (Term.numeral (tag+1)) bv) (bv.get 0) rootCert projCert))) at h
 simpa only [rootCert,projCert,rf,hf,hc,CorrectedAugmentationErasure.certificate,
  CorrectedAugmentationErasure.left,CorrectedAugmentationErasure.middle,CorrectedAugmentationErasure.right,
  av,GraphCalls.nums,GraphValues.args] using h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphProof
