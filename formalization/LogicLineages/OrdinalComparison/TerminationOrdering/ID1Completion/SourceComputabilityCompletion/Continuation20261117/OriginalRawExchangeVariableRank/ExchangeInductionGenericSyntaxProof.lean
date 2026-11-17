module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionFieldsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
open Continuation20261114 Continuation20261115 Continuation20261116
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
open ExchangeInduction
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

def fieldsSchema {alpha : Type} (B : Program 1) (E : Program 2)
    (source target node window lv rv : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing node source target ⊓
    (graph2 E (suc z) node window ⊓ (graph1 B lv source ⊓ graph1 B rv target))
def matrixSchema {alpha : Type} (B : Program 1) (E : Program 2) (source : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  let x : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  (fieldsSchema B E (source.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4)).imp (eqn (x 3) (x 4))
def allSchema {alpha : Type} (B : Program 1) (E : Program 2) (source : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrixSchema B E source)
theorem fieldsSchemaSubst {alpha beta : Type} (B : Program 1) (E : Program 2)
    (source target node window lv rv : OTerm alpha) (ts : alpha → OTerm beta) :
    (fieldsSchema B E source target node window lv rv).subst (fun a => emb (ts a)) =
      fieldsSchema B E (source.subst ts) (target.subst ts) (node.subst ts) (window.subst ts) (lv.subst ts) (rv.subst ts) := by
  simp only [fieldsSchema,conjunctionSubst,graphOneSubst,graphTwoSubst,sucSubst,zSubst]
theorem allSchemaSubst {alpha beta : Type} (B : Program 1) (E : Program 2)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (allSchema B E raw).subst (fun a => emb (ts a)) = allSchema B E (raw.subst ts) := by
  unfold allSchema matrixSchema
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,fieldsSchemaSubst,eqnSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem matrixSchemaWitness {alpha : Type} (B : Program 1) (E : Program 2)
    (source target node window lv rv : OTerm alpha) :
    (matrixSchema B E source).subst (Sum.elim Term.var (fun i => emb (![target,node,window,lv,rv] i))) =
      (fieldsSchema B E source target node window lv rv).imp (eqn lv rv) := by
  have he : (Sum.elim Term.var (fun i => emb (![target,node,window,lv,rv] i))) =
      (fun a => emb (Sum.elim Term.var ![target,node,window,lv,rv] a)) := by
    funext a; cases a <;> rfl
  unfold matrixSchema
  rw [he]
  simp only [impSubst,fieldsSchemaSubst,eqnSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
