module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningRenameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst eqn eqnSubst)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

def observations {alpha : Type} (H : Program 1) (seed param candidate gamma value : OTerm alpha) : Formula alpha :=
  graph2 OriginalClassCodes.gamma gamma seed param ⊓
  graph2 (OriginalTypedDecoder.packedCheck H) value candidate gamma ⊓
  (eqn value (numeral 0)).not

def matrix {alpha : Type} (H : Program 1) (seed param candidate : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  observations H (seed.relabel Sum.inl) (param.relabel Sum.inl) (candidate.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

theorem frozenBlock {alpha : Type} (H : Program 1) (seed param candidate : OTerm alpha) :
    Targets.retained H seed param candidate = InternalFiniteBlocks.block (matrix H seed param candidate) := rfl

theorem observationsSubst {alpha beta : Type} (H : Program 1)
    (seed param candidate gamma value : OTerm alpha) (ts : alpha → OTerm beta) :
    (observations H seed param candidate gamma value).subst (fun a => emb (ts a)) =
      observations H (seed.subst ts) (param.subst ts) (candidate.subst ts) (gamma.subst ts) (value.subst ts) := by
  unfold observations
  simp only [conjunctionSubst,notSubst,eqnSubst,graph2,programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst]

@[simp] theorem observationsRename {alpha beta : Type} (H : Program 1)
    (seed param candidate gamma value : OTerm alpha) (j : alpha → beta) :
    (observations H seed param candidate gamma value).relabel j =
      observations H (seed.relabel j) (param.relabel j) (candidate.relabel j) (gamma.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observations H seed param candidate gamma value).subst (fun a => emb (.var (j a))) = _
  rw [observationsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (H : Program 1) (seed param candidate gamma value : OTerm alpha) :
    (matrix H seed param candidate).subst (Sum.elim Term.var (fun i => emb ((![gamma,value] : Fin 2 → OTerm alpha) i))) =
      observations H seed param candidate gamma value := by
  have he : (Sum.elim Term.var (fun i => emb ((![gamma,value] : Fin 2 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![gamma,value] : Fin 2 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,observationsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem retainedRename {alpha beta : Type} (H : Program 1)
    (seed param candidate : OTerm alpha) (j : alpha → beta) :
    (Targets.retained H seed param candidate).relabel j =
      Targets.retained H (seed.relabel j) (param.relabel j) (candidate.relabel j) := by
  simp only [frozenBlock,InternalOriginalObjectFiberCertifiedLiftSyntaxProof.blockRename,matrix,
    observationsRename,Term.relabel_relabel,Term.relabel]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedSyntaxProof
