module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.MapAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.RawDeletionMapCellProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm row
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalListMap.map OriginalHereditaryDeletionRows.scan

def fields (Q : Program 2) (count input fake typ raw parameter jobs out : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing input typ raw ⊓
    (graph2 InternalPairing.pairing fake z raw ⊓
      (graph3 (OriginalHereditaryDeletionRows.scan OriginalHereditaryExpansion.unpackJob) jobs count fake parameter ⊓
        graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) out jobs typ))

def rowBody (Q : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (fields Q (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
      (graph3 (OriginalHereditaryDeletionRows.scan Q) (.var (.inr 6)) (count.relabel Sum.inl)
        (.var (.inr 0)) (.var (.inr 4)))

def row (Q : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (rowBody Q count)

theorem fieldsSubst {beta : Type} (Q : Program 2)
    (count input fake typ raw parameter jobs out : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields Q count input fake typ raw parameter jobs out).subst (fun a => emb (ts a)) =
      fields Q (count.subst ts) (input.subst ts) (fake.subst ts) (typ.subst ts)
        (raw.subst ts) (parameter.subst ts) (jobs.subst ts) (out.subst ts) := by
  simp only [fields,conjunctionSubst,graph2,graph3,programSubst,consTermSubst,emptySubst,zSubst]

theorem fieldsRename {beta : Type} (Q : Program 2)
    (count input fake typ raw parameter jobs out : OTerm alpha) (j : alpha → beta) :
    (fields Q count input fake typ raw parameter jobs out).relabel j =
      fields Q (count.relabel j) (input.relabel j) (fake.relabel j) (typ.relabel j)
        (raw.relabel j) (parameter.relabel j) (jobs.relabel j) (out.relabel j) := by
  simp only [fields,conjunctionRename,graph2Rename,graph3Rename,zRelabel]

theorem rowSubst {beta : Type} (Q : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row Q count).subst (fun a => emb (ts a)) = row Q (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,graph3,programSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (Q : Program 2) (count : OTerm alpha) (j : alpha → beta) :
    (row Q count).relabel j = row Q (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row Q count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowWitness (Q : Program 2) (count input fake typ raw parameter jobs out : OTerm alpha) :
    (rowBody Q count).subst
      (Sum.elim Term.var (fun i => emb (![input,fake,typ,raw,parameter,jobs,out] i))) =
      (fields Q count input fake typ raw parameter jobs out).imp
        (graph3 (OriginalHereditaryDeletionRows.scan Q) out count input parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,fake,typ,raw,parameter,jobs,out] i))) =
      (fun x => emb (Sum.elim Term.var ![input,fake,typ,raw,parameter,jobs,out] x)) := by
    funext x
    cases x <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,graph3,programSubst,consTermSubst,emptySubst,
    witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate (Q : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row Q count) (emb t) = row Q (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor (Q : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row Q count) = row Q (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

theorem rowApply (Q : Program 2) (count input fake typ raw parameter jobs out : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (fields Q count input fake typ raw parameter jobs out))) :
    Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.scan Q) out count input parameter)) := by
  have h := actualFiniteUniversalElimination body alpha 7 Delta (rowBody Q count)
    (fun i => emb (![input,fake,typ,raw,parameter,jobs,out] i)) hi
  rw [rowWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionScanSyntaxProof
