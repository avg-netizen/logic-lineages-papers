module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
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

def fields  (vb code i : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess i vb ⊓ graph1 OriginalRawSyntaxTransport.variableConstructor code i
def matrix  (vb code : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  fields (vb.relabel Sum.inl) (code.relabel Sum.inl) (.var (.inr 0))

theorem fieldsSubst {beta : Type}  (vb code i : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields vb code i).subst (fun a => emb (sub a)) = fields (vb.subst sub) (code.subst sub) (i.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,numeral,zSubst,sucSubst,InternalLessThan.strictLess,
    InternalQuotientComparisonSyntaxProof.orderSubst,OriginalContextInsertionSyntaxProof.lengthSubst,
    OriginalTypeListsMembership.MemberSyntaxProof.membersSubst]

theorem fieldsRename {beta : Type}  (vb code i : OTerm alpha) (j : alpha → beta) :
    (fields vb code i).relabel j = fields (vb.relabel j) (code.relabel j) (i.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields vb code i).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness  (vb code : OTerm alpha) (ys : Fin 1 → OTerm alpha) :
    (matrix vb code).subst (Sum.elim Term.var (fun i => emb (ys i))) = fields vb code (ys 0) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem caseSubst {beta : Type}  (vb code : OTerm alpha) (sub : alpha → OTerm beta) :
    (Targets.variableCase vb code).subst (fun a => emb (sub a)) = Targets.variableCase (vb.subst sub) (code.subst sub) := by
  change (InternalFiniteBlocks.block (matrix vb code)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix (vb.subst sub) (code.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem caseRename {beta : Type}  (vb code : OTerm alpha) (j : alpha → beta) :
    (Targets.variableCase vb code).relabel j = Targets.variableCase (vb.relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.variableCase vb code).subst (fun a => emb (.var (j a))) = _
  rw [caseSubst]
  simp only [← termRelabelAsSubst]

theorem introduce  (vb code : OTerm alpha) (ys : Fin 1 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields vb code (ys 0)))) :
    Nonempty (Derivation body Delta (Targets.variableCase vb code)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix vb code)))
  apply InternalFiniteBlocksProof.introduction body alpha 1 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases  (vb code : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Targets.variableCase vb code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 1 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields (vb.relabel j) (code.relabel j) (ys 0))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Delta (matrix vb code) psi hf
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let Theta := matrix vb code :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 1) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.VariableSyntaxProof
