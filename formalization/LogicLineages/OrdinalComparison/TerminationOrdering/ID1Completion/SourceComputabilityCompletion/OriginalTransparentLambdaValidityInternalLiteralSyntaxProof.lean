module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLiteralSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb suc z sucSubst zSubst)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)

def literalFields {alpha : Type} (raw d e b typ : OTerm alpha) : Formula alpha :=
  OriginalLambdaConstructor.Fields raw d e b typ ⊓
    graph3 OriginalLambdaConstructor.constructor raw d e b

def literalMatrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  literalFields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3))

theorem literalFieldsSubst {alpha beta : Type} (raw d e b typ : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (literalFields raw d e b typ).subst (fun a => emb (ts a)) =
      literalFields (raw.subst ts) (d.subst ts) (e.subst ts) (b.subst ts) (typ.subst ts) := by
  simp only [literalFields,OriginalLambdaConstructor.Fields,conjunctionSubst,graph1,graph2,graph3,
    programSubst,consTermSubst,emptySubst,numeral,sucSubst,zSubst]

theorem literalMatrixWitness {alpha : Type} (raw d e b typ : OTerm alpha) :
    (literalMatrix raw).subst (Sum.elim Term.var (fun i => emb (![d,e,b,typ] i))) =
      literalFields raw d e b typ := by
  have he : (Sum.elim Term.var (fun i => emb (![d,e,b,typ] i))) =
      (fun a => emb (Sum.elim Term.var ![d,e,b,typ] a)) := by
    funext a; cases a <;> rfl
  unfold literalMatrix
  rw [he,literalFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem literalIntro {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (raw d e b typ : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (literalFields raw d e b typ))) :
    Nonempty (Derivation body Gamma (LiteralLambda raw)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 4 Gamma (literalMatrix raw)
    (fun i => emb (![d,e,b,typ] i))
  rw [literalMatrixWitness]
  exact h

theorem literalCases {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
    (raw : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Gamma (LiteralLambda raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta))
      (d e b typ : OTerm beta), (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (literalFields (raw.relabel j) d e b typ)) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 4 Gamma (literalMatrix raw) psi h
  apply step (alpha ⊕ Fin 4) Sum.inl (literalMatrix raw :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem literalSubst {alpha beta : Type} (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (LiteralLambda raw).subst (fun a => emb (ts a)) = LiteralLambda (raw.subst ts) := by
  change (InternalFiniteBlocks.block (literalMatrix raw)).subst (fun a => emb (ts a)) =
    InternalFiniteBlocks.block (literalMatrix (raw.subst ts))
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold literalMatrix
  simp only [literalFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem literalRename {alpha beta : Type} (raw : OTerm alpha) (j : alpha → beta) :
    (LiteralLambda raw).relabel j = LiteralLambda (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (LiteralLambda raw).subst (fun a => emb (.var (j a))) = _
  rw [literalSubst]
  simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLiteralSyntaxProof
