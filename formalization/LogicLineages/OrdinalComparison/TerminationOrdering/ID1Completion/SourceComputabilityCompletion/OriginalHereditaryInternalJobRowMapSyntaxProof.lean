module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalHereditaryInternalAgenda
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst numeralSubst)
open InternalFiniteBlocks (block)
open OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalJobRow
open OriginalHereditaryInternalJobRowSyntaxProof
open InternalListInduction InternalListInductionSyntaxProof
def mapFields (H : Program 1) (M W : Program 2) (row c B tagged : OTerm alpha) : Formula alpha :=
 Jobs H M W c B row ⊓ graph1 OriginalHereditaryVisitScheduler.tagVisits tagged row
def mapMatrix (H : Program 1) (M W : Program 2) (row : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (mapFields H M W (row.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (Agenda H M W (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)))
def mapRow (H : Program 1) (M W : Program 2) (row : OTerm alpha) : Formula alpha := allBlock (mapMatrix H M W row)
theorem mapFieldsSubst {beta : Type} (H : Program 1) (M W : Program 2) (row c B tagged : OTerm alpha) (ts : alpha → OTerm beta) :
 (mapFields H M W row c B tagged).subst (fun a => emb (ts a)) =
 mapFields H M W (row.subst ts) (c.subst ts) (B.subst ts) (tagged.subst ts) := by
 simp only [mapFields,conjunctionSubst,jobsSubst,graph1,programSubst,consTermSubst,emptySubst]
theorem mapRowSubst {beta : Type} (H : Program 1) (M W : Program 2) (row : OTerm alpha) (ts : alpha → OTerm beta) :
 (mapRow H M W row).subst (fun a => emb (ts a)) = mapRow H M W (row.subst ts) := by
 unfold mapRow mapMatrix
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [mapFieldsSubst,agendaSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem mapRowRename {beta : Type} (H : Program 1) (M W : Program 2) (row : OTerm alpha) (j : alpha → beta) :
 (mapRow H M W row).relabel j = mapRow H M W (row.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (mapRow H M W row).subst (fun a => emb (.var (j a))) = _
 rw [mapRowSubst]
 simp only [← termRelabelAsSubst]
theorem mapWitness (H : Program 1) (M W : Program 2) (row c B tagged : OTerm alpha) :
 (mapMatrix H M W row).subst (Sum.elim Term.var (fun i => emb (![c,B,tagged] i))) =
 (mapFields H M W row c B tagged).imp (Agenda H M W c B tagged) := by
 have he : (Sum.elim Term.var (fun i => emb (![c,B,tagged] i))) =
  (fun a => emb (Sum.elim Term.var ![c,B,tagged] a)) := by funext a; cases a <;> rfl
 unfold mapMatrix
 rw [he,impSubst]
 simp only [mapFieldsSubst,agendaSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem mapApply (H : Program 1) (M W : Program 2) (row c B tagged : OTerm alpha)
 (h : Nonempty (Derivation body Delta (mapRow H M W row)))
 (hf : Nonempty (Derivation body Delta (mapFields H M W row c B tagged))) :
 Nonempty (Derivation body Delta (Agenda H M W c B tagged)) := by
 have hh := actualFiniteUniversalElimination body alpha 3 Delta (mapMatrix H M W row)
  (fun i => emb (![c,B,tagged] i)) h
 rw [mapWitness] at hh
 obtain ⟨hh⟩ := hh
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination hh hf⟩
theorem mapAtCode (H : Program 1) (M W : Program 2) (row : OTerm alpha) :
 atCode (mapRow H M W (.var (.inr (0 : Fin 1)))) row = mapRow H M W row := by
 simp only [atCode,instantiate,bindEmbedding,mapRowSubst,varBind]
theorem mapAtIndex (H : Program 1) (M W : Program 2) (i : Fin 3) :
 atIndex (mapRow H M W (.var (.inr (0 : Fin 1)) : OTerm (alpha ⊕ Fin 1))) i =
 mapRow H M W (.var (.inr i) : OTerm (alpha ⊕ Fin 3)) := by
 rw [atIndex,mapRowRename]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapSyntaxProof
