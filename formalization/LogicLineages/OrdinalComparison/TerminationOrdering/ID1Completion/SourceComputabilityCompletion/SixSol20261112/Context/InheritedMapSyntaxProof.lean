module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.MapAppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb varBind bindEmbedding)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalListInduction InternalListInductionSyntaxProof
open InheritedMapDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map

def fields (Q : Program 2) (jobs typ annotated row : OTerm alpha) : Formula alpha :=
  graph2 (InternalListMap.map (k := 1) inheritedJob) annotated jobs typ ⊓
    graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) row annotated

def rowBody (Q : Program 2) (jobs : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (fields Q (jobs.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
    (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q))
      (.var (.inr 2)) (jobs.relabel Sum.inl) (.var (.inr 0)))

def row (Q : Program 2) (jobs : OTerm alpha) : Formula alpha := allBlock (rowBody Q jobs)

theorem fieldsSubst {beta : Type} (Q : Program 2) (jobs typ annotated row : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (fields Q jobs typ annotated row).subst (fun a => emb (ts a)) =
      fields Q (jobs.subst ts) (typ.subst ts) (annotated.subst ts) (row.subst ts) := by
  simp only [fields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]

theorem fieldsRename {beta : Type} (Q : Program 2) (jobs typ annotated row : OTerm alpha)
    (j : alpha → beta) :
    (fields Q jobs typ annotated row).relabel j =
      fields Q (jobs.relabel j) (typ.relabel j) (annotated.relabel j) (row.relabel j) := by
  simp only [fields,conjunctionRename,graph1Rename,graph2Rename]

theorem rowSubst {beta : Type} (Q : Program 2) (jobs : OTerm alpha) (ts : alpha → OTerm beta) :
    (row Q jobs).subst (fun a => emb (ts a)) = row Q (jobs.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (Q : Program 2) (jobs : OTerm alpha) (j : alpha → beta) :
    (row Q jobs).relabel j = row Q (jobs.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row Q jobs).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowWitness (Q : Program 2) (jobs typ annotated valueRow : OTerm alpha) :
    (rowBody Q jobs).subst (Sum.elim Term.var (fun i => emb (![typ,annotated,valueRow] i))) =
      (fields Q jobs typ annotated valueRow).imp
        (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow jobs typ) := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,annotated,valueRow] i))) =
      (fun x => emb (Sum.elim Term.var ![typ,annotated,valueRow] x)) := by
    funext x
    cases x <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph2,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowAtCode (Q : Program 2) (jobs : OTerm alpha) :
    atCode (row Q (.var (.inr (0 : Fin 1)))) jobs = row Q jobs := by
  simp only [atCode,instantiate,bindEmbedding,rowSubst,varBind]

theorem rowAtIndex (Q : Program 2) (i : Fin 3) :
    atIndex (row Q (.var (.inr (0 : Fin 1)) : OTerm (alpha ⊕ Fin 1))) i =
      row Q (.var (.inr i) : OTerm (alpha ⊕ Fin 3)) := by
  rw [atIndex,rowRename]
  rfl

theorem rowApply (Q : Program 2) (jobs typ annotated valueRow : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row Q jobs)))
    (hf : Nonempty (Derivation body Delta (fields Q jobs typ annotated valueRow))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) valueRow jobs typ)) := by
  have h := actualFiniteUniversalElimination body alpha 3 Delta (rowBody Q jobs)
    (fun i => emb (![typ,annotated,valueRow] i)) hi
  rw [rowWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapSyntaxProof
