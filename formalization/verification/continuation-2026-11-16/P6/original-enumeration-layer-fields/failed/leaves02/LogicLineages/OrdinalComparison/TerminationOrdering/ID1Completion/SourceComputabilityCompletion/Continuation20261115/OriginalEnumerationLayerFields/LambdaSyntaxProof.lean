module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def fields  (types opened code t child : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) types t ⊓ graph2 contains (numeral 1) opened child ⊓ graph2 OriginalRawSyntaxTransport.lambdaConstructor code t child
def matrix  (types opened code : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  fields (types.relabel Sum.inl) (opened.relabel Sum.inl) (code.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))

theorem fieldsSubst {beta : Type}  (types opened code t child : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields types opened code t child).subst (fun a => emb (sub a)) = fields (types.subst sub) (opened.subst sub) (code.subst sub) (t.subst sub) (child.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,numeral,zSubst,sucSubst,InternalLessThan.strictLess,
    InternalQuotientComparisonSyntaxProof.orderSubst,OriginalContextInsertionSyntaxProof.lengthSubst,
    OriginalTypeListsMembership.MemberSyntaxProof.membersSubst]

theorem fieldsRename {beta : Type}  (types opened code t child : OTerm alpha) (j : alpha → beta) :
    (fields types opened code t child).relabel j = fields (types.relabel j) (opened.relabel j) (code.relabel j) (t.relabel j) (child.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields types opened code t child).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness  (types opened code : OTerm alpha) (ys : Fin 2 → OTerm alpha) :
    (matrix types opened code).subst (Sum.elim Term.var (fun i => emb (ys i))) = fields types opened code (ys 0) (ys 1) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem caseSubst {beta : Type}  (types opened code : OTerm alpha) (sub : alpha → OTerm beta) :
    (Targets.lambdaCase types opened code).subst (fun a => emb (sub a)) = Targets.lambdaCase (types.subst sub) (opened.subst sub) (code.subst sub) := by
  change (InternalFiniteBlocks.block (matrix types opened code)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix (types.subst sub) (opened.subst sub) (code.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem caseRename {beta : Type}  (types opened code : OTerm alpha) (j : alpha → beta) :
    (Targets.lambdaCase types opened code).relabel j = Targets.lambdaCase (types.relabel j) (opened.relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.lambdaCase types opened code).subst (fun a => emb (.var (j a))) = _
  rw [caseSubst]
  simp only [← termRelabelAsSubst]

theorem introduce  (types opened code : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields types opened code (ys 0) (ys 1)))) :
    Nonempty (Derivation body Delta (Targets.lambdaCase types opened code)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix types opened code)))
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases  (types opened code : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Targets.lambdaCase types opened code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 2 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields (types.relabel j) (opened.relabel j) (code.relabel j) (ys 0) (ys 1))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (matrix types opened code) psi hf
  let j : alpha → alpha ⊕ Fin 2 := Sum.inl
  let Theta := matrix types opened code :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 2) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.LambdaSyntaxProof
