module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.PersistenceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.RelationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
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
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def matrix (bound old next : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  (Below (.var (.inr 0)) (suc (bound.relabel Sum.inl)) ⊓
    graph2 InternalRawListRecursion.lookup (suc z) (.var (.inr 0)) (old.relabel Sum.inl)).imp
      (graph2 InternalRawListRecursion.lookup (suc z) (.var (.inr 0)) (next.relabel Sum.inl))
def relation (bound old next : OTerm alpha) : Formula alpha := allBlock (matrix bound old next)

theorem relationSubst {beta : Type} (bound old next : OTerm alpha) (ts : alpha → OTerm beta) :
    (relation bound old next).subst (fun a => emb (ts a)) =
      relation (bound.subst ts) (old.subst ts) (next.subst ts) := by
  unfold relation matrix
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,
    sucSubst,zSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem relationRename {beta : Type} (bound old next : OTerm alpha) (j : alpha → beta) :
    (relation bound old next).relabel j = relation (bound.relabel j) (old.relabel j) (next.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (relation bound old next).subst (fun a => emb (.var (j a))) = _
  rw [relationSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness (bound old next index : OTerm alpha) :
    (matrix bound old next).subst (Sum.elim Term.var (fun _ => emb index)) =
      (Below index (suc bound) ⊓ graph2 InternalRawListRecursion.lookup (suc z) index old).imp
        (graph2 InternalRawListRecursion.lookup (suc z) index next) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb index)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => index) a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,impSubst]
  simp only [conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,
    sucSubst,zSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem relationApply (bound old next index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (relation bound old next)))
    (hb : Nonempty (Derivation body Delta (Below index (suc bound))))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index old))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index next)) := by
  have h := actualFiniteUniversalElimination body alpha 1 Delta (matrix bound old next) (fun _ => emb index) hr
  rw [matrixWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro hb hl
  exact ⟨Derivation.implicationElimination h hp⟩

theorem fromRow (n : Nat) (fuel bound old next : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (PersistenceSyntaxProof.row n fuel)))
    (ho : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) old fuel bound)))
    (hn : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) next (suc fuel) bound))) :
    Nonempty (Derivation body Delta (relation bound old next)) := by
  unfold relation
  apply actualFiniteUniversalIntroduction body alpha 1 Delta
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let index : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := Below index (suc (bound.relabel j)) ⊓
    graph2 InternalRawListRecursion.lookup (suc z) index (old.relabel j)
  let Theta := A :: Delta.map (fun p => p.relabel j)
  have hj : ∀ p ∈ Delta, p.relabel j ∈ Theta :=
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [PersistenceSyntaxProof.rowRename] at hr'
  have ho' := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  have hn' := InternalGraphCompositionFunctionalityProof.renameInto hn j Theta hj
  simp only [graph2Rename,sucRelabel] at ho' hn'
  have ha : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := PersistenceSyntaxProof.rowApply n (fuel.relabel j) (bound.relabel j)
    (old.relabel j) (next.relabel j) index hr' (andIntro (andIntro ho' hn') ha)
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.RelationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.RelationProof
