module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb suc z sucSubst zSubst)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)

def sourceFields {alpha : Type} (data : Data) (raw parameter typ d e : OTerm alpha) : Formula alpha :=
  graph1 InternalUnpair.left typ raw ⊓
    (graph1 OriginalLambdaConstructor.domain d raw ⊓
      (graph1 InternalListCodec.tailCode e typ ⊓
        (graph2 OriginalLambdaConstructor.arrow typ d e ⊓
          (graph2 data.member (numeral 1) typ parameter ⊓ graph2 data.member (numeral 1) d parameter))))

def sourceMatrix {alpha : Type} (data : Data) (raw parameter : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  sourceFields data (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem sourceFieldsSubst {alpha beta : Type} (data : Data) (raw parameter typ d e : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (sourceFields data raw parameter typ d e).subst (fun a => emb (ts a)) =
      sourceFields data (raw.subst ts) (parameter.subst ts) (typ.subst ts) (d.subst ts) (e.subst ts) := by
  simp only [sourceFields,conjunctionSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,
    numeral,sucSubst,zSubst]

theorem sourceMatrixWitness {alpha : Type} (data : Data) (raw parameter typ d e : OTerm alpha) :
    (sourceMatrix data raw parameter).subst (Sum.elim Term.var (fun i => emb (![typ,d,e] i))) =
      sourceFields data raw parameter typ d e := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,d,e] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,d,e] a)) := by
    funext a; cases a <;> rfl
  unfold sourceMatrix
  rw [he,sourceFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem sourceIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (data : Data) (raw parameter typ d e : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (sourceFields data raw parameter typ d e))) :
    Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 3 Gamma (sourceMatrix data raw parameter)
    (fun i => emb (![typ,d,e] i))
  rw [sourceMatrixWitness]
  exact h

theorem sourceCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (data : Data) (raw parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (typ d e : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (sourceFields data (raw.relabel j) (parameter.relabel j) typ d e)) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Gamma (sourceMatrix data raw parameter) psi h
  apply step (alpha ⊕ Fin 3) Sum.inl
    (sourceMatrix data raw parameter :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem sourceSubst {alpha beta : Type} (data : Data) (raw parameter : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (SourceLambdaRootFactors data raw parameter).subst (fun a => emb (ts a)) =
      SourceLambdaRootFactors data (raw.subst ts) (parameter.subst ts) := by
  change (InternalFiniteBlocks.block (sourceMatrix data raw parameter)).subst (fun a => emb (ts a)) =
    InternalFiniteBlocks.block (sourceMatrix data (raw.subst ts) (parameter.subst ts))
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold sourceMatrix
  simp only [sourceFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem sourceRename {alpha beta : Type} (data : Data) (raw parameter : OTerm alpha)
    (j : alpha → beta) :
    (SourceLambdaRootFactors data raw parameter).relabel j =
      SourceLambdaRootFactors data (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (SourceLambdaRootFactors data raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [sourceSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceSyntaxProof
