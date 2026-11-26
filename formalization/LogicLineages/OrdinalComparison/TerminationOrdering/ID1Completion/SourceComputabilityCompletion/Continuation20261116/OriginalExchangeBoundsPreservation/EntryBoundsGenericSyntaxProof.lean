module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EntryBounds
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

def fieldsSchema {alpha : Type} (C W : Program 1) (X : Program 2)
    (raw param entries value : OTerm alpha) : Formula alpha :=
  graph1 C (suc z) raw ⊓ (graph2 X (suc entries) raw param ⊓ graph1 W value entries)
def matrixSchema {alpha : Type} (C W B : Program 1) (X : Program 2) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  (fieldsSchema C W X (raw.relabel Sum.inl) (x 0) (x 1) (x 2)).imp
    (graph1 B (x 2) (raw.relabel Sum.inl))
def allSchema {alpha : Type} (C W B : Program 1) (X : Program 2) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrixSchema C W B X raw)
theorem fieldsSchemaSubst {alpha beta : Type} (C W : Program 1) (X : Program 2) (raw param entries value : OTerm alpha) (ts : alpha → OTerm beta) :
    (fieldsSchema C W X raw param entries value).subst (fun a => emb (ts a)) =
      fieldsSchema C W X (raw.subst ts) (param.subst ts) (entries.subst ts) (value.subst ts) := by
  simp only [fieldsSchema,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,sucSubst,zSubst]
theorem allSchemaSubst {alpha beta : Type} (C W B : Program 1) (X : Program 2) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (allSchema C W B X raw).subst (fun a => emb (ts a)) = allSchema C W B X (raw.subst ts) := by
  unfold allSchema matrixSchema
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSchemaSubst,graph1,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]
theorem matrixSchemaWitness {alpha : Type} (C W B : Program 1) (X : Program 2) (raw param entries value : OTerm alpha) :
    (matrixSchema C W B X raw).subst (Sum.elim Term.var (fun i => emb (![param,entries,value] i))) =
      (fieldsSchema C W X raw param entries value).imp (graph1 B value raw) := by
  have he : (Sum.elim Term.var (fun i => emb (![param,entries,value] i))) =
      (fun a => emb (Sum.elim Term.var ![param,entries,value] a)) := by
    funext a; cases a <;> rfl
  unfold matrixSchema
  rw [he]
  simp only [impSubst,fieldsSchemaSubst,graph1,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSyntaxProof
