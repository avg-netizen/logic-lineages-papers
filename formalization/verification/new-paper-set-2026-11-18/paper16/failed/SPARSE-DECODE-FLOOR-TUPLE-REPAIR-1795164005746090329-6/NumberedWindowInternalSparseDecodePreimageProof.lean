module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodePreimageProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDecodeTargets NumberedWindowInternalSparseDecodeSyntaxProof

abbrev sparsePair := NumberedWindowInternalSparsePair.pair

def second {α : Type} (n x : OTerm α) : Formula α :=
  existsOne (binary sparsePair (n.relabel Sum.inl) (x.relabel Sum.inl) (.var (.inr 0)))

private theorem secondRename {α β : Type} (n x : OTerm α) (j : α → β) :
    (second n x).relabel j = second (n.relabel j) (x.relabel j) := by
  simp only [second,existsRename,binaryRename,Term.relabel_relabel,Term.relabel] <;> rfl

theorem preimageRename {α β : Type} (n : OTerm α) (j : α → β) :
    (hasPreimage n).relabel j = hasPreimage (n.relabel j) := by
  change (existsOne (second (n.relabel Sum.inl) (.var (.inr 0)))).relabel j =
    existsOne (second ((n.relabel j).relabel Sum.inl) (.var (.inr 0)))
  simp only [existsRename,secondRename,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem binarySubst {α β : Type} (p : Program 2) (n x y : OTerm α) (ts : α → OTerm β) :
    (binary p n x y).subst (fun a => emb (ts a)) =
      binary p (n.subst ts) (x.subst ts) (y.subst ts) := by
  unfold binary programGraph
  rw [graphSubst]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

private theorem secondSubst {α β : Type} (n x : OTerm α) (ts : α → OTerm β) :
    (second n x).subst (fun a => emb (ts a)) = second (n.subst ts) (x.subst ts) := by
  unfold second
  rw [existsSubst,liftedEmbedding,binarySubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem preimageIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (n x y : OTerm α) (h : Nonempty (Derivation body Γ (binary sparsePair n x y))) :
    Nonempty (Derivation body Γ (hasPreimage n)) := by
  obtain ⟨h⟩ := h
  have inner : Derivation body Γ (second n x) := by
    unfold second
    apply Derivation.existentialIntroduction (emb y)
    rw [instantiate,bindEmbedding,binarySubst]
    simp only [liftBind,varBind]
    exact h
  apply Nonempty.intro
  change Derivation body Γ (existsOne (second (n.relabel Sum.inl) (.var (.inr 0))))
  apply Derivation.existentialIntroduction (emb x)
  rw [instantiate,bindEmbedding,secondSubst,liftBind,varBind]
  exact inner

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodePreimageProof
