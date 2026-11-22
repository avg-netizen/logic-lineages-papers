module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucRelabel sucSubst zSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseMinimumBoundTargets

attribute [local irreducible] programGraph

private theorem notRename {α β : Type} (p : Formula α) (j : α → β) :
    p.not.relabel j = (p.relabel j).not := rfl

private theorem notSubst {α β : Type} (p : Formula α) (ts : α → Term β) :
    p.not.subst ts = (p.subst ts).not := rfl

theorem rowRename {α β : Type} (code k val : OTerm α) (j : α → β) :
    (boundedRow code k val).relabel j =
      boundedRow (code.relabel j) (k.relabel j) (val.relabel j) := by
  simp only [boundedRow,conjunctionRename,unaryRename,sucRelabel,notRename,
    ID1Completion.InternalLessThan.strictLess,orderRename]

private theorem rowSubst {α β : Type} (code k val : OTerm α) (ts : α → OTerm β) :
    (boundedRow code k val).subst (fun a => emb (ts a)) =
      boundedRow (code.subst ts) (k.subst ts) (val.subst ts) := by
  simp only [boundedRow,conjunctionSubst,unarySubst,sucSubst,notSubst,
    ID1Completion.InternalLessThan.strictLess,orderSubst]

abbrev boundBinder {α : Type} (code k : OTerm α) : Formula (α ⊕ Fin 1) :=
  boundedRow (code.relabel Sum.inl) (k.relabel Sum.inl) (.var (.inr 0))

theorem witnessUnfold {α : Type} (code k : OTerm α) :
    boundedWitness code k = existsOne (boundBinder code k) := rfl

theorem binderValue {α : Type} (code k val : OTerm α) :
    instantiate (boundBinder code k) (emb val) = boundedRow code k val := by
  simp only [instantiate,boundBinder,bindEmbedding,rowSubst,liftBind,varBind]

theorem witnessRename {α β : Type} (code k : OTerm α) (j : α → β) :
    (boundedWitness code k).relabel j = boundedWitness (code.relabel j) (k.relabel j) := by
  rw [witnessUnfold,witnessUnfold,existsRename]
  unfold boundBinder
  rw [rowRename]
  simp only [Term.relabel_relabel]
  rfl

theorem witnessSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (boundedWitness code k).subst (fun a => emb (ts a)) = boundedWitness (code.subst ts) (k.subst ts) := by
  unfold boundedWitness
  rw [existsSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) = memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) = ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

abbrev memberBound {α : Type} (code k : OTerm α) : Formula α :=
  (memberGraph code k).imp (boundedWitness code k)

theorem boundRename {α β : Type} (code k : OTerm α) (j : α → β) :
    (memberBound code k).relabel j = memberBound (code.relabel j) (k.relabel j) := by
  change ((memberGraph code k).relabel j).imp ((boundedWitness code k).relabel j) = _
  rw [graphRename,witnessRename]

abbrev invariant {α : Type} (k : OTerm α) : Formula (α ⊕ Fin 1) :=
  memberBound (.var (.inr 0)) (k.relabel Sum.inl)

theorem invariantCode {α : Type} (k code : OTerm α) :
    atCode (invariant k) code = memberBound code k := by
  rw [atCode,instantiate,bindEmbedding]
  change (memberBound (.var (.inr 0)) (k.relabel Sum.inl)).subst _ = _
  simp only [memberBound,impSubst,memberSubst,witnessSubst,liftBind,varBind]

theorem invariantIndex {α : Type} (k : OTerm α) (i : Fin 3) :
    atIndex (invariant k) i = memberBound (.var (.inr i)) (k.relabel Sum.inl) := by
  unfold atIndex
  change (memberBound (.var (.inr 0)) (k.relabel Sum.inl)).relabel _ = _
  rw [boundRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundSyntaxProof
