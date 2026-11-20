module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof (acceptanceRename)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph finishRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets

theorem positiveRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (positiveAt raw least ctx ty source cert target).relabel j =
      positiveAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
        (cert.relabel j) (target.relabel j) :=
  acceptanceRename raw least ctx ty source cert target j

theorem finishAtRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (finishAt raw least ctx ty source cert target).relabel j =
      finishAt raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
        (cert.relabel j) (target.relabel j) := by
  change (finishGraph raw least (suc target) ctx ty (suc source) cert).relabel j = _
  rw [finishRename] <;> simp only [sucRelabel] <;> rfl

theorem finishedRename {α β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source cert target : OTerm α) (j : α → β) :
    (finishedNonempty raw least ctx ty source cert target).relabel j =
      finishedNonempty raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
        (cert.relabel j) (target.relabel j) := by
  simp only [finishedNonempty,equalEqn]
  change ((eqn cert z).relabel j).not ⊓
    (finishAt raw least ctx ty source cert target).relabel j = _
  rw [eqnRelabel,zRelabel,finishAtRename]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
