module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof

def fields {alpha : Type} (out raw typ : OTerm alpha) : Formula alpha :=
  graph1 InternalUnpair.left typ raw ⊓ graph1 InternalListCodec.tailCode out typ

def matrix {alpha : Type} (out raw : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  fields (out.relabel Sum.inl) (raw.relabel Sum.inl) (.var (.inr 0))

theorem fieldsSubst {alpha beta : Type} (out raw typ : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields out raw typ).subst (fun a => emb (ts a)) =
      fields (out.subst ts) (raw.subst ts) (typ.subst ts) := by
  simp only [fields,conjunctionSubst,graph1,programSubst,consTermSubst,emptySubst]

theorem matrixWitness {alpha : Type} (out raw typ : OTerm alpha) :
    (matrix out raw).subst (Sum.elim Term.var (fun _ : Fin 1 => emb typ)) =
      fields out raw typ := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb typ)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => typ) a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem codomainIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (out raw typ : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (fields out raw typ))) :
    Nonempty (Derivation body Gamma (CodomainGraph out raw)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 1 Gamma (matrix out raw)
    (fun _ : Fin 1 => emb typ)
  rw [matrixWitness]
  exact h

theorem codomainCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (out raw : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (CodomainGraph out raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (typ : OTerm beta),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (fields (out.relabel j) (raw.relabel j) typ)) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Gamma (matrix out raw) psi h
  apply step (alpha ⊕ Fin 1) Sum.inl (matrix out raw :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem codomainSubst {alpha beta : Type} (out raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (CodomainGraph out raw).subst (fun a => emb (ts a)) =
      CodomainGraph (out.subst ts) (raw.subst ts) := by
  change (InternalFiniteBlocks.block (matrix out raw)).subst (fun a => emb (ts a)) =
    InternalFiniteBlocks.block (matrix (out.subst ts) (raw.subst ts))
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold matrix
  simp only [fieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem codomainRename {alpha beta : Type} (out raw : OTerm alpha) (j : alpha → beta) :
    (CodomainGraph out raw).relabel j = CodomainGraph (out.relabel j) (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (CodomainGraph out raw).subst (fun a => emb (.var (j a))) = _
  rw [codomainSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorSyntaxProof
