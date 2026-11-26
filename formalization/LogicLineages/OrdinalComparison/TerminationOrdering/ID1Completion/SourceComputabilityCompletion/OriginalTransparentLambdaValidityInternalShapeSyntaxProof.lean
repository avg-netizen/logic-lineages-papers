module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof

def shapeFields {alpha : Type} (raw typ d e : OTerm alpha) : Formula alpha :=
  graph1 InternalUnpair.left typ raw ⊓
    (graph1 OriginalLambdaConstructor.domain d raw ⊓
      (graph1 InternalListCodec.tailCode e typ ⊓ graph2 OriginalLambdaConstructor.arrow typ d e))

def shapeMatrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  shapeFields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem shapeFieldsSubst {alpha beta : Type} (raw typ d e : OTerm alpha) (ts : alpha → OTerm beta) :
    (shapeFields raw typ d e).subst (fun a => emb (ts a)) =
      shapeFields (raw.subst ts) (typ.subst ts) (d.subst ts) (e.subst ts) := by
  simp only [shapeFields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst]

theorem shapeMatrixWitness {alpha : Type} (raw typ d e : OTerm alpha) :
    (shapeMatrix raw).subst (Sum.elim Term.var (fun i => emb (![typ,d,e] i))) =
      shapeFields raw typ d e := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,d,e] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,d,e] a)) := by
    funext a; cases a <;> rfl
  unfold shapeMatrix
  rw [he,shapeFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem shapeIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (raw typ d e : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (shapeFields raw typ d e))) :
    Nonempty (Derivation body Gamma (LambdaShape raw)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 3 Gamma (shapeMatrix raw)
    (fun i => emb (![typ,d,e] i))
  rw [shapeMatrixWitness]
  exact h

theorem shapeCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (raw : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (LambdaShape raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (typ d e : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (shapeFields (raw.relabel j) typ d e)) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Gamma (shapeMatrix raw) psi h
  apply step (alpha ⊕ Fin 3) Sum.inl (shapeMatrix raw :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem shapeSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (LambdaShape raw).subst (fun a => emb (ts a)) = LambdaShape (raw.subst ts) := by
  change (InternalFiniteBlocks.block (shapeMatrix raw)).subst (fun a => emb (ts a)) =
    InternalFiniteBlocks.block (shapeMatrix (raw.subst ts))
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold shapeMatrix
  simp only [shapeFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem shapeRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (LambdaShape raw).relabel j = LambdaShape (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (LambdaShape raw).subst (fun a => emb (.var (j a))) = _
  rw [shapeSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeSyntaxProof
