module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellExistentialProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open NumberedWindowInternalSparseFieldInductionTargets
open NumberedWindowInternalSparseFieldExistentialProof (consGraphSubst)

private theorem tailSubst {α β : Type} (n h : OTerm α) (ts : α → OTerm β) :
    (someTail n h).subst (fun a => emb (ts a)) = someTail (n.subst ts) (h.subst ts) := by
  unfold someTail
  rw [existsSubst,liftedEmbedding,consGraphSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem someConsIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (n h t : OTerm α) (d : Nonempty (Derivation body Γ (consGraph n h t))) :
    Nonempty (Derivation body Γ (someCons n)) := by
  obtain ⟨d⟩ := d
  have inner : Derivation body Γ (someTail n h) := by
    unfold someTail
    apply Derivation.existentialIntroduction (emb t)
    rw [instantiate,bindEmbedding,consGraphSubst]
    simp only [liftBind,varBind]
    exact d
  apply Nonempty.intro
  unfold someCons
  apply Derivation.existentialIntroduction (emb h)
  rw [instantiate,bindEmbedding,tailSubst,liftBind,varBind]
  exact inner

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellExistentialProof
