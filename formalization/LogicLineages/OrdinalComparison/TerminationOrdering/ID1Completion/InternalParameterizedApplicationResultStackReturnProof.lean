module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackCompositionFrameSupportProof
open InternalApplicationResultStackCompositionFrameConstructorsProof
open InternalApplicationResultStackReturnSupportProof InternalApplicationResultStackReturnRelationProof
open InternalParameterizedApplicationResultStackWiringProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open InternalParameterizedApplicationResultStack InternalParameterizedApplicationResultStackReturnSupportProof

theorem leafBackward (guard leaf : Program 2) (combine : Program 5)
    (value work results state out parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value work results)))
    (hg : Nonempty (Derivation body Gamma (graph2 (openGuardP guard) z value parameter)))
    (ho : Nonempty (Derivation body Gamma (returned leaf out
      (Fin.cons value (Fin.cons parameter Fin.elim0)) work results))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  apply visitStateCases state value work results _ hs
  intro β j Delta frame stack hj hsl hc hp
  simp only [graph2Rename]
  have hg' := renameInto hg j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph2Rename,zRelabel] at hg'
  simp only [returnedRename,consTermRename,emptyRename] at ho'
  apply returnedCases leaf (out.relabel j)
    (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (work.relabel j) (results.relabel j) _ ho'
  intro γ k Theta leafValue hk hl hr
  simp only [graph2Rename]
  simp only [consTermRename,emptyRename] at hl
  have hsl' := renameInto hsl k Theta hk
  have hc' := renameInto hc k Theta hk
  have hp' := renameInto hp k Theta hk
  have hg'' := renameInto hg' k Theta hk
  simp only [graph2Rename,zRelabel] at hsl' hc' hp' hg''
  exact leafAt guard leaf combine ((state.relabel j).relabel k) (stack.relabel k)
    ((results.relabel j).relabel k) (frame.relabel k) ((value.relabel j).relabel k)
    ((work.relabel j).relabel k) ((out.relabel j).relabel k) ((parameter.relabel j).relabel k)
    leafValue hsl' hc' hp' hg'' hl hr

theorem finishBackward (guard leaf : Program 2) (combine : Program 5)
    (d e work argument function results state out parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph6 finishState state d e work argument function results)))
    (ho : Nonempty (Derivation body Gamma (returned combine out
      (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0))))) work results))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  apply finishStateCases state d e work argument function results _ hs
  intro β j Delta value frame stack afterArgument oldResults hj hsl hc hp hv hr ht
  simp only [graph2Rename]
  have ho' := renameInto ho j Delta hj
  simp only [returnedRename,consTermRename,emptyRename] at ho'
  apply returnedCases combine (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (function.relabel j)
      (Fin.cons (argument.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))))
    (work.relabel j) (results.relabel j) _ ho'
  intro γ k Theta combinedValue hk hcomb hret
  simp only [graph2Rename]
  simp only [consTermRename,emptyRename] at hcomb
  have hsl' := renameInto hsl k Theta hk
  have hc' := renameInto hc k Theta hk
  have hp' := renameInto hp k Theta hk
  have hv' := renameInto hv k Theta hk
  have hr' := renameInto hr k Theta hk
  have ht' := renameInto ht k Theta hk
  simp only [graph2Rename,zRelabel,sucRelabel] at hsl' hc' hp' hv' hr' ht'
  exact finishAt guard leaf combine ((state.relabel j).relabel k) (stack.relabel k)
    (oldResults.relabel k) (frame.relabel k) (value.relabel k)
    ((d.relabel j).relabel k) ((e.relabel j).relabel k) ((work.relabel j).relabel k)
    ((argument.relabel j).relabel k) ((function.relabel j).relabel k) ((results.relabel j).relabel k)
    (afterArgument.relabel k) ((out.relabel j).relabel k) ((parameter.relabel j).relabel k)
    combinedValue hsl' hc' hp' hv' hr' ht' hcomb hret

/-- Functionality and totality turn any internally established return step
into the converse equation, without a callback-specific evaluator. -/
theorem returnedForward {n m : Nat} (p : Program n) (step : Program m)
    (out work results : OTerm α) (xs : Fin n → OTerm α) (ss : Fin m → OTerm α)
    (ho : Nonempty (Derivation body Gamma (programGraph step out ss)))
    (back : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v r : OTerm β),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph p v (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (graph3 returnState r v (work.relabel j) (results.relabel j))) →
      Nonempty (Derivation body Delta (programGraph step r (fun i => (ss i).relabel j)))) :
    Nonempty (Derivation body Gamma (returned p out xs work results)) := by
  apply programCases p xs _
  intro β j Delta v hj hp
  simp only [returnedRename]
  apply programCases returnState (Fin.cons v (Fin.cons (work.relabel j) (Fin.cons (results.relabel j) Fin.elim0))) _
  intro γ k Theta r hk hr
  simp only [returnedRename,Term.relabel_relabel]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp k Theta hk
  simp only [programRename,Term.relabel_relabel] at hp'
  have hr' : Nonempty (Derivation body Theta
      (graph3 returnState r (v.relabel k) (work.relabel (k ∘ j)) (results.relabel (k ∘ j)))) := by
    simpa only [Term.relabel_relabel] using hr
  have hctx : ∀ q ∈ Gamma, q.relabel (k ∘ j) ∈ Theta := by
    intro q hq
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (q.relabel j) (hj q hq)
  have hs := back γ (k ∘ j) Theta (v.relabel k) r hctx hp' hr'
  have ho' := renameInto ho (k ∘ j) Theta hctx
  simp only [programRename] at ho'
  have he := valueUnique step r (out.relabel (k ∘ j)) _ hs ho'
  exact returnedIntro p (out.relabel (k ∘ j)) (fun i => (xs i).relabel (k ∘ j))
    (work.relabel (k ∘ j)) (results.relabel (k ∘ j)) (v.relabel k) hp'
    (outputTransport returnState r (out.relabel (k ∘ j)) _ he hr')

theorem leafForward (guard leaf : Program 2) (combine : Program 5)
    (value work results state out parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value work results)))
    (hg : Nonempty (Derivation body Gamma (graph2 (openGuardP guard) z value parameter)))
    (ho : Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter))) :
    Nonempty (Derivation body Gamma (returned leaf out
      (Fin.cons value (Fin.cons parameter Fin.elim0)) work results)) := by
  apply returnedForward leaf (transitionP guard leaf combine) out work results
    (Fin.cons value (Fin.cons parameter Fin.elim0)) (Fin.cons state (Fin.cons parameter Fin.elim0)) ho
  intro β j Delta v r hj hl hr
  simp only [consTermRename,emptyRename] at hl ⊢
  have hs' := renameInto hs j Delta hj
  have hg' := renameInto hg j Delta hj
  simp only [graph3Rename,graph2Rename,zRelabel] at hs' hg'
  exact leafBackward guard leaf combine (value.relabel j) (work.relabel j) (results.relabel j)
    (state.relabel j) r (parameter.relabel j) hs' hg'
    (returnedIntro leaf r _ (work.relabel j) (results.relabel j) v hl hr)

theorem finishForward (guard leaf : Program 2) (combine : Program 5)
    (d e work argument function results state out parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph6 finishState state d e work argument function results)))
    (ho : Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter))) :
    Nonempty (Derivation body Gamma (returned combine out
      (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0))))) work results)) := by
  apply returnedForward combine (transitionP guard leaf combine) out work results
    (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0)))))
    (Fin.cons state (Fin.cons parameter Fin.elim0)) ho
  intro β j Delta v r hj hl hr
  simp only [consTermRename,emptyRename] at hl ⊢
  have hs' := renameInto hs j Delta hj
  simp only [InternalApplicationResultStackReturnFinishSupportProof.graph6Rename] at hs'
  exact finishBackward guard leaf combine (d.relabel j) (e.relabel j) (work.relabel j)
    (argument.relabel j) (function.relabel j) (results.relabel j) (state.relabel j) r (parameter.relabel j) hs'
    (returnedIntro combine r _ (work.relabel j) (results.relabel j) v hl hr)

theorem actualOriginalParameterizedApplicationResultStackLeaf :
    InternalParameterizedApplicationResultStackTargets.ActualOriginalParameterizedApplicationResultStackLeaf := by
  intro body guard leaf combine α Gamma value work results state out parameter
  let c := graph3 visitState state value work results ⊓ graph2 (openGuardP guard) z value parameter
  let g := graph2 (transitionP guard leaf combine) out state parameter
  let r := returned leaf out (Fin.cons value (Fin.cons parameter Fin.elim0)) work results
  have hc₁ : Nonempty (Derivation body (g :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body (r :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := leafForward guard leaf combine value work results state out parameter
    (andLeft hc₁) (andRight hc₁) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := leafBackward guard leaf combine value work results state out parameter
    (andLeft hc₂) (andRight hc₂) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualOriginalParameterizedApplicationResultStackFinish :
    InternalParameterizedApplicationResultStackTargets.ActualOriginalParameterizedApplicationResultStackFinish := by
  intro body guard leaf combine α Gamma d e work argument function results state out parameter
  let c := graph6 finishState state d e work argument function results
  let g := graph2 (transitionP guard leaf combine) out state parameter
  let r := returned combine out (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0))))) work results
  have hc₁ : Nonempty (Derivation body (g :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body (r :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := finishForward guard leaf combine d e work argument function results state out parameter
    hc₁ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := finishBackward guard leaf combine d e work argument function results state out parameter
    hc₂ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnProof
