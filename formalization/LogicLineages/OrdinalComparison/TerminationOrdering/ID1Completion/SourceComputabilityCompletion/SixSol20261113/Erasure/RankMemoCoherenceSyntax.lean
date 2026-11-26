module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoherenceSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalListCodec SourceComputabilityFormulaSupportProof
open InternalRawListRecursionSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionSyntaxProof InternalRecursionGraphStepSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRecursionClosureSyntaxProof InternalClosedPrograms InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)

def dropBody {α : Type} (gap : OTerm α) : Formula (α ⊕ Fin 3) :=
  (graph1 RankMemoDefinitions.table (.var (.inr 1)) (.var (.inr 0)) ⊓
    graph1 RankMemoDefinitions.table (.var (.inr 2))
      (OrdinaryArithmetic.addTerm (.var (.inr 0)) (gap.relabel Sum.inl))).imp
    (dropGraph (.var (.inr 1)) (gap.relabel Sum.inl) (.var (.inr 2)))

/-- Every older table is reached by exactly its index difference many tails. -/
def dropRow {α : Type} (gap : OTerm α) : Formula α :=
  allBlock (dropBody gap)

theorem dropRowSubst {α β : Type} (gap : OTerm α) (ts : α → OTerm β) :
    (dropRow gap).subst (fun a => emb (ts a)) =
      dropRow (gap.subst ts) := by
  unfold dropRow dropBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [graph1,dropGraph,programSubst,consTermSubst,InternalAdditionLawsProof.addSubst,
    liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem dropRowRename {α β : Type} (gap : OTerm α) (j : α → β) :
    (dropRow gap).relabel j =
      dropRow (gap.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (dropRow gap).subst (fun a => emb (.var (j a))) = _
  rw [dropRowSubst]
  simp only [← termRelabelAsSubst]

theorem dropBodyWitness {α : Type} (gap code small large : OTerm α) :
    (dropBody gap).subst
      (Sum.elim Term.var (fun i => emb (![code,small,large] i))) =
      (graph1 RankMemoDefinitions.table small code ⊓
        graph1 RankMemoDefinitions.table large (OrdinaryArithmetic.addTerm code gap)).imp
          (dropGraph small gap large) := by
  have he : (Sum.elim Term.var (fun i => emb (![code,small,large] i))) =
      (fun a => emb (Sum.elim Term.var ![code,small,large] a)) := by
    funext a
    cases a <;> rfl
  unfold dropBody
  rw [he,impSubst,conjunctionSubst]
  simp only [graph1,dropGraph,programSubst,consTermSubst,InternalAdditionLawsProof.addSubst,
    witnessLift,Term.subst,Sum.elim_inr,emptySubst]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoherenceSyntax

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoCoherenceSyntax
