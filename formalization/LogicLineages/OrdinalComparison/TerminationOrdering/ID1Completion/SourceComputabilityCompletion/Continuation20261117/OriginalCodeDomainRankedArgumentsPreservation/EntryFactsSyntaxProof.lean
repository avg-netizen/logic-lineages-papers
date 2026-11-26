module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EntryFacts
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem querySubst {beta : Type} (entries needle hits : OTerm alpha) (ts : alpha → OTerm beta) :
    (query entries needle hits).subst (fun a => emb (ts a)) =
      query (entries.subst ts) (needle.subst ts) (hits.subst ts) := by
  simp only [query,conjunctionSubst,impSubst,notSubst,
    graph2,programSubst,consTermSubst,emptySubst,eqnSubst,zSubst]

theorem queryRename {beta : Type} (entries needle hits : OTerm alpha) (j : alpha → beta) :
    (query entries needle hits).relabel j = query (entries.relabel j) (needle.relabel j) (hits.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (query entries needle hits).subst (fun a => emb (.var (j a))) = _
  rw [querySubst]
  simp only [← termRelabelAsSubst]

theorem allGoodSubst {beta : Type} (H : Program 1) (M W : Program 2)
    (entries gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (allGood H M W entries gamma context).subst (fun a => emb (ts a)) =
      allGood H M W (entries.subst ts) (gamma.subst ts) (context.subst ts) := by
  unfold allGood matrix
  rw [allBlockSubst,liftedEmbedding,impSubst,querySubst]
  simp only [graph3,programSubst,consTermSubst,emptySubst,zSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem allGoodRename {beta : Type} (H : Program 1) (M W : Program 2)
    (entries gamma context : OTerm alpha) (j : alpha → beta) :
    (allGood H M W entries gamma context).relabel j =
      allGood H M W (entries.relabel j) (gamma.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allGood H M W entries gamma context).subst (fun a => emb (.var (j a))) = _
  rw [allGoodSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (H : Program 1) (M W : Program 2) (entries gamma context needle hits : OTerm alpha) :
    (matrix H M W entries gamma context).subst (Sum.elim Term.var (fun i => emb (![needle,hits] i))) =
      (query entries needle hits).imp (graph3 (entryCheck H M W) (suc z) needle gamma context) := by
  have he : (Sum.elim Term.var (fun i => emb (![needle,hits] i))) =
      (fun a => emb (Sum.elim Term.var ![needle,hits] a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he,impSubst,querySubst]
  simp only [graph3,programSubst,consTermSubst,emptySubst,zSubst,sucSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem allGoodApply (H : Program 1) (M W : Program 2) (entries gamma context needle hits : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (allGood H M W entries gamma context)))
    (hq : Nonempty (Derivation body Delta (query entries needle hits))) :
    Nonempty (Derivation body Delta (graph3 (entryCheck H M W) (suc z) needle gamma context)) := by
  have h := actualFiniteUniversalElimination body alpha 2 Delta (matrix H M W entries gamma context)
    (fun i => emb (![needle,hits] i)) ha
  rw [matrixWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.implicationElimination h hq⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsSyntaxProof
