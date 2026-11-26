module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind sucRelabel sucSubst zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (parserRename)
open NumberedWindowInternalSparseOrderedMinimum (orderedPoolMinimum scratchMinimum)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRawMinimumOccurrence

attribute [local irreducible] programGraph

abbrev binder {α : Type} (raw selected : OTerm α) : Formula (α ⊕ Fin 1) :=
  parsedOccurrenceRow (raw.relabel Sum.inl) (.var (.inr 0)) (selected.relabel Sum.inl)

theorem occurrenceUnfold {α : Type} (raw selected : OTerm α) :
    parsedOccurrence raw selected = existsOne (binder raw selected) := rfl

theorem rawMinimumRename {α β : Type} (raw selected : OTerm α) (j : α → β) :
    (rawMinimumGraph raw selected).relabel j =
      rawMinimumGraph (raw.relabel j) (selected.relabel j) := by
  simp only [rawMinimumGraph,unaryRename,sucRelabel]

private theorem rowRename {α β : Type} (raw scratch selected : OTerm α) (j : α → β) :
    (parsedOccurrenceRow raw scratch selected).relabel j =
      parsedOccurrenceRow (raw.relabel j) (scratch.relabel j) (selected.relabel j) := by
  simp only [parsedOccurrenceRow,conjunctionRename,parserRename,unaryRename,graphRename,sucRelabel]

theorem occurrenceRename {α β : Type} (raw selected : OTerm α) (j : α → β) :
    (parsedOccurrence raw selected).relabel j =
      parsedOccurrence (raw.relabel j) (selected.relabel j) := by
  rw [occurrenceUnfold,occurrenceUnfold,existsRename]
  unfold binder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

private theorem parserSubst {α β : Type} (out raw : OTerm α) (ts : α → OTerm β) :
    (parserGraph out raw).subst (fun a => emb (ts a)) =
      parserGraph (out.subst ts) (raw.subst ts) :=
  unarySubst parser out raw ts

private theorem rowSubst {α β : Type} (raw scratch selected : OTerm α) (ts : α → OTerm β) :
    (parsedOccurrenceRow raw scratch selected).subst (fun a => emb (ts a)) =
      parsedOccurrenceRow (raw.subst ts) (scratch.subst ts) (selected.subst ts) := by
  simp only [parsedOccurrenceRow,conjunctionSubst,parserSubst,unarySubst,memberSubst,sucSubst]

theorem occurrenceInstance {α : Type} (raw scratch selected : OTerm α) :
    instantiate (binder raw selected) (emb scratch) = parsedOccurrenceRow raw scratch selected := by
  simp only [instantiate,binder,bindEmbedding,rowSubst,liftBind,varBind]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenSyntaxProof
