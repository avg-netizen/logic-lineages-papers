module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalHereditaryValidity OriginalHereditaryValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields {α : Type} (member : Program 2) (raw parameter typ tag : OTerm α) : Formula α :=
  graph1 InternalUnpair.left typ raw ⊓ (graph1 OriginalLambdaConstructor.tag tag raw ⊓
    (equal tag (numeral 2)).imp (graph2 member (numeral 1) typ parameter))
def matrix {α : Type} (member : Program 2) (raw parameter : OTerm α) : Formula (α ⊕ Fin 2) :=
  fields member (raw.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
def someFields {α : Type} (member : Program 2) (raw parameter : OTerm α) : Formula α :=
  InternalFiniteBlocks.block (matrix member raw parameter)

theorem eqnRename {α β : Type} (s t : OTerm α) (j : α → β) :
    (eqn s t).relabel j = eqn (s.relabel j) (t.relabel j) := by
  rw [eqn,InternalDerivationRenamingSyntaxProof.equalityRename,
    ← InternalBinderTransportSyntaxProof.onTermRelabel,
    ← InternalBinderTransportSyntaxProof.onTermRelabel]
  rfl

theorem impRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p.imp q).relabel j = (p.relabel j).imp (q.relabel j) := rfl

@[simp] theorem fieldsRename {α β : Type} (member : Program 2) (raw parameter typ tag : OTerm α) (j : α → β) :
    (fields member raw parameter typ tag).relabel j = fields member (raw.relabel j) (parameter.relabel j) (typ.relabel j) (tag.relabel j) := by
  simp only [fields,conjunctionRename,impRename,graph1Rename,graph2Rename,equalEqn,eqnRename,numeral,sucRelabel,zRelabel]

theorem fieldsSubst {α β : Type} (member : Program 2) (raw parameter typ tag : OTerm α) (ts : α → OTerm β) :
    (fields member raw parameter typ tag).subst (fun a => emb (ts a)) =
      fields member (raw.subst ts) (parameter.subst ts) (typ.subst ts) (tag.subst ts) := by
  simp only [fields,conjunctionSubst,impSubst,graph1,graph2,programSubst,consTermSubst,emptySubst,equalEqn,eqnSubst,numeral,sucSubst,zSubst]

theorem matrixWitness {α : Type} (member : Program 2) (raw parameter typ tag : OTerm α) :
    (matrix member raw parameter).subst (Sum.elim Term.var (fun i => emb (![typ,tag] i))) = fields member raw parameter typ tag := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,tag] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,tag] a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem fieldsIntro {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (member : Program 2) (raw parameter typ tag : OTerm α)
    (h : Nonempty (Derivation body Gamma (fields member raw parameter typ tag))) :
    Nonempty (Derivation body Gamma (someFields member raw parameter)) := by
  apply InternalFiniteBlocksProof.introduction body α 2 Gamma (matrix member raw parameter)
    (fun i => emb (![typ,tag] i))
  rw [matrixWitness]
  exact h

theorem fieldsCases {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (member : Program 2) (raw parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (someFields member raw parameter)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (typ tag : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (fields member (raw.relabel j) (parameter.relabel j) typ tag)) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply InternalFiniteBlocksProof.elimination body α 2 Gamma (matrix member raw parameter) psi h
  apply step (α ⊕ Fin 2) Sum.inl (matrix member raw parameter :: Gamma.map (fun p => p.relabel Sum.inl))
    (.var (.inr 0)) (.var (.inr 1))
  · intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem someFieldsSubst {α β : Type} (member : Program 2) (raw parameter : OTerm α) (ts : α → OTerm β) :
    (someFields member raw parameter).subst (fun a => emb (ts a)) = someFields member (raw.subst ts) (parameter.subst ts) := by
  unfold someFields InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold matrix
  simp only [fieldsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem someFieldsRename {α β : Type} (member : Program 2) (raw parameter : OTerm α) (j : α → β) :
    (someFields member raw parameter).relabel j = someFields member (raw.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (someFields member raw parameter).subst (fun a => emb (.var (j a))) = _
  rw [someFieldsSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem factorsRename {α β : Type} (s t m : Program 2) (raw parameter : OTerm α) (j : α → β) :
    (NodeFactors s t m raw parameter).relabel j = NodeFactors s t m (raw.relabel j) (parameter.relabel j) := by
  change (graph2 s (numeral 1) raw parameter ⊓ (graph2 t (numeral 1) raw parameter ⊓ someFields m raw parameter)).relabel j = _
  simp only [conjunctionRename,graph2Rename,someFieldsRename,numeral,sucRelabel,zRelabel]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSyntaxProof
