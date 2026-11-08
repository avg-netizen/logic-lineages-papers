module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnRelationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackReturnSupportProof InternalApplicationResultStackReturnRelationProof
open InternalApplicationResultStackReturnLeafSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem leafForward (guard leaf : Program 1) (combine : Program 4)
    (value work results state out : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value work results)))
    (hg : Nonempty (Derivation body Gamma (graph1 (openGuard guard) z value)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state))) :
    Nonempty (Derivation body Gamma (leafResult leaf out value work results)) := by
  apply queryCases (queries leaf) (Fin.cons value (Fin.cons work (Fin.cons results Fin.elim0))) _
  intro β j ys Delta hj hq
  simp only [leafResultRename]
  rw [leafResultEqReturned]
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  have hg' := renameInto hg j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph3Rename,graph1Rename,zRelabel] at hs' hg' ho'
  have ht := transitionFromQueries guard leaf combine (value.relabel j) (work.relabel j)
    (results.relabel j) (state.relabel j) ys hs' hg' hq
  have hr := returnFromQueries leaf (value.relabel j) (work.relabel j) (results.relabel j) ys hq
  have heq := valueUnique (transition guard leaf combine) (ys 6) (out.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) ht ho'
  exact returnedIntro leaf (out.relabel j) (Fin.cons (value.relabel j) Fin.elim0)
    (work.relabel j) (results.relabel j) (ys 3) hr.1
    (outputTransport returnState (ys 6) (out.relabel j) _ heq hr.2)

theorem leafBackward (guard leaf : Program 1) (combine : Program 4)
    (value work results state out : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value work results)))
    (hg : Nonempty (Derivation body Gamma (graph1 (openGuard guard) z value)))
    (ho : Nonempty (Derivation body Gamma (leafResult leaf out value work results))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state)) := by
  apply queryCases (queries leaf) (Fin.cons value (Fin.cons work (Fin.cons results Fin.elim0))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename]
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  have hg' := renameInto hg j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph3Rename,graph1Rename,zRelabel,leafResultRename] at hs' hg' ho'
  rw [leafResultEqReturned] at ho'
  have ht := transitionFromQueries guard leaf combine (value.relabel j) (work.relabel j)
    (results.relabel j) (state.relabel j) ys hs' hg' hq
  have hr := returnFromQueries leaf (value.relabel j) (work.relabel j) (results.relabel j) ys hq
  have hr' := returnedRecover leaf (out.relabel j) (Fin.cons (value.relabel j) Fin.elim0)
    (work.relabel j) (results.relabel j) (ys 3) ho' hr.1
  have heq := valueUnique returnState (ys 6) (out.relabel j)
    (Fin.cons (ys 3) (Fin.cons (work.relabel j) (Fin.cons (results.relabel j) Fin.elim0))) hr.2 hr'
  exact outputTransport (transition guard leaf combine) (ys 6) (out.relabel j) _ heq ht

theorem actualOriginalResultStackLeaf : InternalApplicationResultStackTargets.ActualOriginalResultStackLeaf := by
  intro body guard leaf combine α value work results state out
  let c := graph3 visitState state value work results ⊓ graph1 (openGuard guard) z value
  let g := graph1 (transition guard leaf combine) out state
  let r := leafResult leaf out value work results
  have hc₁ : Nonempty (Derivation body [g,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body [r,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := leafForward guard leaf combine value work results state out
    (andLeft hc₁) (andRight hc₁) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := leafBackward guard leaf combine value work results state out
    (andLeft hc₂) (andRight hc₂) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafProof
