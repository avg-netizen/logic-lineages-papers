module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalExtensionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFactorSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb eqnSubst sucSubst zSubst)
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidityInternalExtensionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof
open OriginalHereditaryValidityInternalNodeSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalAdditionLawsProof (impSubst)

def tagFields {alpha : Type} (s t m : Program 2) (raw parameter tag : OTerm alpha) : Formula alpha :=
  graph1 OriginalLambdaConstructor.tag tag raw ⊓
    (((equal tag (numeral 2)).imp (RootApplicationChildren s t m raw parameter)) ⊓
      ((equal tag (numeral 1)).imp (RootLambdaChild s t m raw parameter)))

def tagMatrix {alpha : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  tagFields s t m (raw.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0))

def tagBlock {alpha : Type} (s t m : Program 2) (raw parameter : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (tagMatrix s t m raw parameter)

theorem tagFieldsSubst {alpha beta : Type} (s t m : Program 2)
    (raw parameter tag : OTerm alpha) (ts : alpha → OTerm beta) :
    (tagFields s t m raw parameter tag).subst (fun a => emb (ts a)) =
      tagFields s t m (raw.subst ts) (parameter.subst ts) (tag.subst ts) := by
  simp only [tagFields,conjunctionSubst,impSubst,graph1,programSubst,consTermSubst,
    emptySubst,equalEqn,eqnSubst,rootApplicationSubst,rootLambdaSubst,numeral,sucSubst,zSubst]

theorem tagMatrixWitness {alpha : Type} (s t m : Program 2) (raw parameter tag : OTerm alpha) :
    (tagMatrix s t m raw parameter).subst
      (Sum.elim Term.var (fun i => emb (![tag] i))) = tagFields s t m raw parameter tag := by
  unfold tagMatrix
  rw [witnessEmbedding,tagFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem tagBlockSubst {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (tagBlock s t m raw parameter).subst (fun a => emb (ts a)) =
      tagBlock s t m (raw.subst ts) (parameter.subst ts) := by
  unfold tagBlock InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold tagMatrix
  simp only [tagFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem tagBlockRename {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (j : alpha → beta) :
    (tagBlock s t m raw parameter).relabel j = tagBlock s t m (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (tagBlock s t m raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [tagBlockSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem recurrenceRename {alpha beta : Type} (s t m : Program 2)
    (raw parameter : OTerm alpha) (j : alpha → beta) :
    (RecurrenceFactors s t m raw parameter).relabel j =
      RecurrenceFactors s t m (raw.relabel j) (parameter.relabel j) := by
  change (NodeFactors s t m raw parameter ⊓ tagBlock s t m raw parameter).relabel j = _
  simp only [conjunctionRename,factorsRename,tagBlockRename]
  rfl

theorem recurrenceIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (s t m : Program 2) (raw parameter tag : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)))
    (hf : Nonempty (Derivation body Gamma (tagFields s t m raw parameter tag))) :
    Nonempty (Derivation body Gamma (RecurrenceFactors s t m raw parameter)) := by
  apply andIntro hn
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma (tagMatrix s t m raw parameter)
    (fun i => emb (![tag] i))
  rw [tagMatrixWitness]
  exact hf

theorem recurrenceCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (s t m : Program 2) (raw parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (RecurrenceFactors s t m raw parameter)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (tag : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (NodeFactors s t m (raw.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (tagFields s t m (raw.relabel j) (parameter.relabel j) tag)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma (tagMatrix s t m raw parameter)
    psi (andRight h)
  let Delta := tagMatrix s t m raw parameter :: Gamma.map (fun p => p.relabel Sum.inl)
  have inc : ∀ p ∈ Gamma, p.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ Delta := by
    intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hn := renameInto (andLeft h) Sum.inl Delta inc
  rw [factorsRename] at hn
  exact step (alpha ⊕ Fin 1) Sum.inl Delta (.var (.inr 0)) inc hn
    ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFactorSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFactorSyntaxProof
