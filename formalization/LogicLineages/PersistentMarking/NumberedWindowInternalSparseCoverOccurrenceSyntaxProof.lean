module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind sucRelabel sucSubst zSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets

variable (C : Program 3) (s : Settings)

attribute [local irreducible] programGraph

abbrev coverBinder {α : Type} (seed k : OTerm α) : Formula (α ⊕ Fin 1) :=
  coverRow C s (seed.relabel Sum.inl) (k.relabel Sum.inl) (.var (.inr 0))

private theorem unfoldCover {α : Type} (seed k : OTerm α) :
    occursInCover C s seed k = existsOne (coverBinder C s seed k) := rfl

private theorem rowRename {α β : Type} (seed k vertices : OTerm α) (j : α → β) :
    (coverRow C s seed k vertices).relabel j =
      coverRow C s (seed.relabel j) (k.relabel j) (vertices.relabel j) := by
  simp only [coverRow,conjunctionRename,unaryRename,graphRename]

theorem coverRename {α β : Type} (seed k : OTerm α) (j : α → β) :
    (occursInCover C s seed k).relabel j = occursInCover C s (seed.relabel j) (k.relabel j) := by
  rw [unfoldCover,unfoldCover,existsRename]
  unfold coverBinder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

private theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

private theorem rowSubst {α β : Type} (seed k vertices : OTerm α) (ts : α → OTerm β) :
    (coverRow C s seed k vertices).subst (fun a => emb (ts a)) =
      coverRow C s (seed.subst ts) (k.subst ts) (vertices.subst ts) := by
  simp only [coverRow,conjunctionSubst,unarySubst,memberSubst]

theorem coverIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (seed k vertices : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)))
    (member : Nonempty (Derivation body Γ (memberGraph vertices k))) :
    Nonempty (Derivation body Γ (occursInCover C s seed k)) := by
  have inst : instantiate (coverBinder C s seed k) (emb vertices) = coverRow C s seed k vertices := by
    simp only [instantiate,coverBinder,bindEmbedding,rowSubst,liftBind,varBind]
  obtain ⟨a⟩ := cover
  obtain ⟨b⟩ := member
  rw [unfoldCover]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb vertices)
  rw [inst]
  exact Derivation.conjunctionIntroduction a b

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
