module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupSyntaxProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open NumberedWindowInternalSparseFieldParser (scratchBase scratchStep scratchTable scratchRow)
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalRawListRecursion InternalListCodec SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionSyntaxProof InternalRecursionGraphStepSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRecursionClosureSyntaxProof InternalClosedPrograms InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)

open InternalRawListRecursionSyntaxProof
abbrev memoGraph {α : Type} (B : Program 2) (R : Program 4)
    (out code : OTerm α) (params : Fin 2 → OTerm α) : Formula α :=
  programGraph (scratchTable B R) out (Fin.cons code params)


abbrev memoRowGraph {α : Type} (B : Program 2) (R : Program 4)
    (out code : OTerm α) (params : Fin 2 → OTerm α) : Formula α :=
  programGraph (scratchRow B R) out (Fin.cons code params)

@[simp] theorem memoRowRename {α β : Type} (B : Program 2) (R : Program 4)
    (out code : OTerm α) (params : Fin 2 → OTerm α) (j : α → β) :
    (memoRowGraph B R out code params).relabel j =
      memoRowGraph B R (out.relabel j) (code.relabel j) (fun i => (params i).relabel j) := by
  simp only [memoRowGraph,programRename,consTermRename]

@[simp] theorem memoRename {α β : Type} (B : Program 2) (R : Program 4)
    (out code : OTerm α) (params : Fin 2 → OTerm α) (j : α → β) :
    (memoGraph B R out code params).relabel j =
      memoGraph B R (out.relabel j) (code.relabel j) (fun i => (params i).relabel j) := by
  simp only [memoGraph,programRename,consTermRename]

def memoBody {α : Type} (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α) : Formula (α ⊕ Fin 3) :=
  (memoGraph B R (.var (.inr 1)) (.var (.inr 0)) (fun i => (params i).relabel Sum.inl) ⊓
    memoGraph B R (.var (.inr 2))
      (OrdinaryArithmetic.addTerm (.var (.inr 0)) (gap.relabel Sum.inl))
        (fun i => (params i).relabel Sum.inl)).imp
    (dropGraph (.var (.inr 1)) (gap.relabel Sum.inl) (.var (.inr 2)))

/-- Every older table is reached by exactly its index difference many tails. -/
def memoDropRow {α : Type} (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α) : Formula α :=
  allBlock (memoBody B R gap params)

theorem memoDropRowSubst {α β : Type} (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α) (ts : α → OTerm β) :
    (memoDropRow B R gap params).subst (fun a => emb (ts a)) =
      memoDropRow B R (gap.subst ts) (fun i => (params i).subst ts) := by
  unfold memoDropRow memoBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [memoGraph,dropGraph,programSubst,consTermSubst,InternalAdditionLawsProof.addSubst,
    liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem memoDropRowRename {α β : Type} (B : Program 2) (R : Program 4)
    (gap : OTerm α) (params : Fin 2 → OTerm α) (j : α → β) :
    (memoDropRow B R gap params).relabel j =
      memoDropRow B R (gap.relabel j) (fun i => (params i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (memoDropRow B R gap params).subst (fun a => emb (.var (j a))) = _
  rw [memoDropRowSubst]
  simp only [← termRelabelAsSubst]

theorem memoBodyWitness {α : Type} (B : Program 2) (R : Program 4)
    (gap code small large : OTerm α) (params : Fin 2 → OTerm α) :
    (memoBody B R gap params).subst
      (Sum.elim Term.var (fun i => emb (![code,small,large] i))) =
      (memoGraph B R small code params ⊓
        memoGraph B R large (OrdinaryArithmetic.addTerm code gap) params).imp
          (dropGraph small gap large) := by
  have he : (Sum.elim Term.var (fun i => emb (![code,small,large] i))) =
      (fun a => emb (Sum.elim Term.var ![code,small,large] a)) := by
    funext a
    cases a <;> rfl
  unfold memoBody
  rw [he,impSubst,conjunctionSubst]
  simp only [memoGraph,dropGraph,programSubst,consTermSubst,InternalAdditionLawsProof.addSubst,
    witnessLift,Term.subst,Sum.elim_inr,emptySubst]
  rfl


end LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinLookupSyntaxProof
