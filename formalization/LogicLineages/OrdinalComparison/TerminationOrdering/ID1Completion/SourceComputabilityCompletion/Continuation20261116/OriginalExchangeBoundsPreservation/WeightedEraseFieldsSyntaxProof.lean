module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
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
open WeightedErase
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

def effectSchema {alpha : Type} (M : Program 2) (bit total remainingWeight needleWeight : OTerm alpha) : Formula alpha :=
  ((eqn bit z).imp (eqn total remainingWeight)) ⊓
  ((eqn bit (suc z)).imp (graph2 M total needleWeight remainingWeight))
def fieldsSchema {alpha : Type} (S P : Program 2) (F weight : Program 1)
    (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha) : Formula alpha :=
  (graph2 S acc raw needle ⊓ graph2 P acc bit rest) ⊓
  (graph1 F total raw ⊓
   (graph1 F remainingWeight rest ⊓ graph1 weight needleWeight needle))
def matrixSchema {alpha : Type} (S P M : Program 2) (F weight : Program 1) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  let x : Fin 7 → OTerm (alpha ⊕ Fin 7) := fun i => .var (.inr i)
  (fieldsSchema S P F weight (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)).imp
    (effectSchema M (x 2) (x 4) (x 5) (x 6))
def allSchema {alpha : Type} (S P M : Program 2) (F weight : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrixSchema S P M F weight raw)
theorem effectSchemaSubst {alpha beta : Type} (M : Program 2) (bit total remainingWeight needleWeight : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (effectSchema M bit total remainingWeight needleWeight).subst (fun a => emb (ts a)) =
    effectSchema M (bit.subst ts) (total.subst ts) (remainingWeight.subst ts) (needleWeight.subst ts) := by
  unfold effectSchema
  simp only [conjunctionSubst,impSubst,eqnSubst,graph2,programSubst,
    consTermSubst,emptySubst,zSubst,sucSubst]

theorem fieldsSchemaSubst {alpha beta : Type} (S P : Program 2) (F weight : Program 1)
    (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (fieldsSchema S P F weight raw needle acc bit rest total remainingWeight needleWeight).subst (fun a => emb (ts a)) =
    fieldsSchema S P F weight (raw.subst ts) (needle.subst ts) (acc.subst ts) (bit.subst ts) (rest.subst ts)
      (total.subst ts) (remainingWeight.subst ts) (needleWeight.subst ts) := by
  unfold fieldsSchema
  simp only [conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseSyntaxProof
