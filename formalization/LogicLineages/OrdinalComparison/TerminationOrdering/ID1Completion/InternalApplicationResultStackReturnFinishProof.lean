module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnRelationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackReturnSupportProof InternalApplicationResultStackReturnRelationProof
open InternalApplicationResultStackReturnFinishSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem finishForward (guard leaf : Program 1) (combine : Program 4)
    (d e work argument function results state out : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph6 finishState state d e work argument function results)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state))) :
    Nonempty (Derivation body Gamma (finishResult combine out d e work argument function results)) := by
  apply queryCases (queries combine) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results Fin.elim0)))))) _
  intro β j ys Delta hj hq
  simp only [finishResultRename]
  rw [finishResultEqReturned]
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph6Rename,graph1Rename] at hs' ho'
  have ht := transitionFromQueries guard leaf combine (d.relabel j) (e.relabel j) (work.relabel j)
    (argument.relabel j) (function.relabel j) (results.relabel j) (state.relabel j) ys hs' hq
  have hr := returnFromQueries combine (d.relabel j) (e.relabel j) (work.relabel j)
    (argument.relabel j) (function.relabel j) (results.relabel j) ys hq
  have heq := valueUnique (transition guard leaf combine) (ys 9) (out.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) ht ho'
  exact returnedIntro combine (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (function.relabel j) (Fin.cons (argument.relabel j) Fin.elim0))))
    (work.relabel j) (results.relabel j) (ys 6) hr.1
    (outputTransport returnState (ys 9) (out.relabel j) _ heq hr.2)

theorem finishBackward (guard leaf : Program 1) (combine : Program 4)
    (d e work argument function results state out : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph6 finishState state d e work argument function results)))
    (ho : Nonempty (Derivation body Gamma (finishResult combine out d e work argument function results))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state)) := by
  apply queryCases (queries combine) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results Fin.elim0)))))) _
  intro β j ys Delta hj hq
  simp only [graph1Rename]
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph6Rename,graph1Rename,finishResultRename] at hs' ho'
  rw [finishResultEqReturned] at ho'
  have ht := transitionFromQueries guard leaf combine (d.relabel j) (e.relabel j) (work.relabel j)
    (argument.relabel j) (function.relabel j) (results.relabel j) (state.relabel j) ys hs' hq
  have hr := returnFromQueries combine (d.relabel j) (e.relabel j) (work.relabel j)
    (argument.relabel j) (function.relabel j) (results.relabel j) ys hq
  have hr' := returnedRecover combine (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (function.relabel j) (Fin.cons (argument.relabel j) Fin.elim0))))
    (work.relabel j) (results.relabel j) (ys 6) ho' hr.1
  have heq := valueUnique returnState (ys 9) (out.relabel j)
    (Fin.cons (ys 6) (Fin.cons (work.relabel j) (Fin.cons (results.relabel j) Fin.elim0))) hr.2 hr'
  exact outputTransport (transition guard leaf combine) (ys 9) (out.relabel j) _ heq ht

theorem actualOriginalResultStackFinish : InternalApplicationResultStackTargets.ActualOriginalResultStackFinish := by
  intro body guard leaf combine α d e work argument function results state out
  let c := graph6 finishState state d e work argument function results
  let g := graph1 (transition guard leaf combine) out state
  let r := finishResult combine out d e work argument function results
  have hc₁ : Nonempty (Derivation body [g,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body [r,c] c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := finishForward guard leaf combine d e work argument function results state out
    hc₁ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := finishBackward guard leaf combine d e work argument function results state out
    hc₂ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishProof
