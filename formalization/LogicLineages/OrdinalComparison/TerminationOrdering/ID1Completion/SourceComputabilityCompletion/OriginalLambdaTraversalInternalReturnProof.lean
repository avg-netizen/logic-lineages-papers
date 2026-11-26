module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackReturnSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationForwardFromQueries (leaf : Program 2)
    (d e work argument function results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph applicationReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))))))
    (hp : Nonempty (Derivation positive Gamma (graph4 application produced d e function argument)))
    (ys : Fin 10 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation positive Gamma (programGraph (InternalApplicationResultStackReturnFinishSupportProof.queries application i) (ys i) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))))))
    (ho : Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Gamma (graph3 returnState out produced work results)) := by
  have ht := OriginalLambdaTraversalInternalReturnApplicationProof.transitionFromQueries leaf d e work argument function results state ys hs hq
  have hr := InternalApplicationResultStackReturnFinishSupportProof.returnFromQueries application d e work argument function results ys hq
  have heq := valueUnique application (ys 6) produced
    (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.elim0))))) hr.1 hp
  have hr' := headTransport returnState (ys 9) (ys 6) produced
    (Fin.cons work (Fin.cons results (Fin.elim0))) heq hr.2
  exact outputTransport returnState (ys 9) out _
    (valueUnique (transition leaf) (ys 9) out _ ht ho) hr'


theorem applicationForward (leaf : Program 2)
    (d e work argument function results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph applicationReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))))))
    (hp : Nonempty (Derivation positive Gamma (graph4 application produced d e function argument)))
    (ho : Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Gamma (graph3 returnState out produced work results)) := by
  apply queryCases (InternalApplicationResultStackReturnFinishSupportProof.queries application) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))) _
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [graph1Rename,graph3Rename]
  have hs' := renameInto hs j Delta hj
  have hp' := renameInto hp j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hs'
  simp only [graph4Rename] at hp'
  simp only [graph1Rename,graph3Rename] at ho'
  exact applicationForwardFromQueries leaf (d.relabel j) (e.relabel j) (work.relabel j) (argument.relabel j) (function.relabel j) (results.relabel j) (state.relabel j) (produced.relabel j) (out.relabel j) hs' hp' ys hq ho'

theorem applicationBackwardFromQueries (leaf : Program 2)
    (d e work argument function results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph applicationReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))))))
    (hp : Nonempty (Derivation positive Gamma (graph4 application produced d e function argument)))
    (ys : Fin 10 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation positive Gamma (programGraph (InternalApplicationResultStackReturnFinishSupportProof.queries application i) (ys i) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))))))
    (ho : Nonempty (Derivation positive Gamma (graph3 returnState out produced work results))) :
    Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state)) := by
  have ht := OriginalLambdaTraversalInternalReturnApplicationProof.transitionFromQueries leaf d e work argument function results state ys hs hq
  have hr := InternalApplicationResultStackReturnFinishSupportProof.returnFromQueries application d e work argument function results ys hq
  have heq := valueUnique application (ys 6) produced
    (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.elim0))))) hr.1 hp
  have hr' := headTransport returnState (ys 9) (ys 6) produced
    (Fin.cons work (Fin.cons results (Fin.elim0))) heq hr.2
  exact outputTransport (transition leaf) (ys 9) out _
    (valueUnique returnState (ys 9) out _ hr' ho) ht


theorem applicationBackward (leaf : Program 2)
    (d e work argument function results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph applicationReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))))))
    (hp : Nonempty (Derivation positive Gamma (graph4 application produced d e function argument)))
    (ho : Nonempty (Derivation positive Gamma (graph3 returnState out produced work results))) :
    Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state)) := by
  apply queryCases (InternalApplicationResultStackReturnFinishSupportProof.queries application) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))) _
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [graph1Rename,graph3Rename]
  have hs' := renameInto hs j Delta hj
  have hp' := renameInto hp j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hs'
  simp only [graph4Rename] at hp'
  simp only [graph1Rename,graph3Rename] at ho'
  exact applicationBackwardFromQueries leaf (d.relabel j) (e.relabel j) (work.relabel j) (argument.relabel j) (function.relabel j) (results.relabel j) (state.relabel j) (produced.relabel j) (out.relabel j) hs' hp' ys hq ho'

theorem lambdaForwardFromQueries (leaf : Program 2)
    (d e work value results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph lambdaReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))))))
    (hp : Nonempty (Derivation positive Gamma (graph3 OriginalLambdaConstructor.constructor produced d e value)))
    (ys : Fin 9 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation positive Gamma (programGraph (OriginalLambdaTraversalInternalReturnLambdaProof.queries i) (ys i) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))))))
    (ho : Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Gamma (graph3 returnState out produced work results)) := by
  have ht := OriginalLambdaTraversalInternalReturnLambdaProof.transitionFromQueries leaf d e work value results state ys hs hq
  have hr := OriginalLambdaTraversalInternalReturnLambdaProof.returnFromQueries d e work value results ys hq
  have heq := valueUnique OriginalLambdaConstructor.constructor (ys 5) produced
    (Fin.cons d (Fin.cons e (Fin.cons value (Fin.elim0)))) hr.1 hp
  have hr' := headTransport returnState (ys 8) (ys 5) produced
    (Fin.cons work (Fin.cons results (Fin.elim0))) heq hr.2
  exact outputTransport returnState (ys 8) out _
    (valueUnique (transition leaf) (ys 8) out _ ht ho) hr'


theorem lambdaForward (leaf : Program 2)
    (d e work value results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph lambdaReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))))))
    (hp : Nonempty (Derivation positive Gamma (graph3 OriginalLambdaConstructor.constructor produced d e value)))
    (ho : Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Gamma (graph3 returnState out produced work results)) := by
  apply queryCases (OriginalLambdaTraversalInternalReturnLambdaProof.queries) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))) _
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [graph1Rename,graph3Rename]
  have hs' := renameInto hs j Delta hj
  have hp' := renameInto hp j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hs'
  simp only [graph3Rename] at hp'
  simp only [graph1Rename,graph3Rename] at ho'
  exact lambdaForwardFromQueries leaf (d.relabel j) (e.relabel j) (work.relabel j) (value.relabel j) (results.relabel j) (state.relabel j) (produced.relabel j) (out.relabel j) hs' hp' ys hq ho'

theorem lambdaBackwardFromQueries (leaf : Program 2)
    (d e work value results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph lambdaReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))))))
    (hp : Nonempty (Derivation positive Gamma (graph3 OriginalLambdaConstructor.constructor produced d e value)))
    (ys : Fin 9 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation positive Gamma (programGraph (OriginalLambdaTraversalInternalReturnLambdaProof.queries i) (ys i) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))))))
    (ho : Nonempty (Derivation positive Gamma (graph3 returnState out produced work results))) :
    Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state)) := by
  have ht := OriginalLambdaTraversalInternalReturnLambdaProof.transitionFromQueries leaf d e work value results state ys hs hq
  have hr := OriginalLambdaTraversalInternalReturnLambdaProof.returnFromQueries d e work value results ys hq
  have heq := valueUnique OriginalLambdaConstructor.constructor (ys 5) produced
    (Fin.cons d (Fin.cons e (Fin.cons value (Fin.elim0)))) hr.1 hp
  have hr' := headTransport returnState (ys 8) (ys 5) produced
    (Fin.cons work (Fin.cons results (Fin.elim0))) heq hr.2
  exact outputTransport (transition leaf) (ys 8) out _
    (valueUnique returnState (ys 8) out _ hr' ho) ht


theorem lambdaBackward (leaf : Program 2)
    (d e work value results state produced out : OTerm α)
    (hs : Nonempty (Derivation positive Gamma (programGraph lambdaReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))))))
    (hp : Nonempty (Derivation positive Gamma (graph3 OriginalLambdaConstructor.constructor produced d e value)))
    (ho : Nonempty (Derivation positive Gamma (graph3 returnState out produced work results))) :
    Nonempty (Derivation positive Gamma (graph1 (transition leaf) out state)) := by
  apply queryCases (OriginalLambdaTraversalInternalReturnLambdaProof.queries) (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))) _
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  simp only [graph1Rename,graph3Rename]
  have hs' := renameInto hs j Delta hj
  have hp' := renameInto hp j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hs'
  simp only [graph3Rename] at hp'
  simp only [graph1Rename,graph3Rename] at ho'
  exact lambdaBackwardFromQueries leaf (d.relabel j) (e.relabel j) (work.relabel j) (value.relabel j) (results.relabel j) (state.relabel j) (produced.relabel j) (out.relabel j) hs' hp' ys hq ho'

theorem actualOriginalLambdaTraversalInternalReturns :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalReturns := by
  intro positive leaf α Delta
  constructor
  · intro d e work argument function results state produced out
    let c := programGraph applicationReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results (Fin.elim0))))))) ⊓ graph4 application produced d e function argument
    let g := graph1 (transition leaf) out state
    let r := graph3 returnState out produced work results
    have hc₁ : Nonempty (Derivation positive (g :: c :: Delta) c) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hc₂ : Nonempty (Derivation positive (r :: c :: Delta) c) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨hf⟩ := applicationForward leaf d e work argument function results state produced out
      (andLeft hc₁) (andRight hc₁) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hb⟩ := applicationBackward leaf d e work argument function results state produced out
      (andLeft hc₂) (andRight hc₂) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
  · intro d e work value results state produced out
    let c := programGraph lambdaReturnState state (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons value (Fin.cons results (Fin.elim0)))))) ⊓ graph3 OriginalLambdaConstructor.constructor produced d e value
    let g := graph1 (transition leaf) out state
    let r := graph3 returnState out produced work results
    have hc₁ : Nonempty (Derivation positive (g :: c :: Delta) c) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hc₂ : Nonempty (Derivation positive (r :: c :: Delta) c) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨hf⟩ := lambdaForward leaf d e work value results state produced out
      (andLeft hc₁) (andRight hc₁) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hb⟩ := lambdaBackward leaf d e work value results state produced out
      (andLeft hc₂) (andRight hc₂) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnProof
