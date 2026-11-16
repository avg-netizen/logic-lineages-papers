module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomSyntaxProof
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

def fields  (types code t : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) types t ⊓ graph1 OriginalRawSyntaxTransport.bottomConstructor code t
def matrix  (types code : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  fields (types.relabel Sum.inl) (code.relabel Sum.inl) (.var (.inr 0))

theorem fieldsSubst {beta : Type}  (types code t : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields types code t).subst (fun a => emb (sub a)) = fields (types.subst sub) (code.subst sub) (t.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,numeral,zSubst,sucSubst,InternalLessThan.strictLess,
    InternalQuotientComparisonSyntaxProof.orderSubst,OriginalContextInsertionSyntaxProof.lengthSubst,
    OriginalTypeListsMembership.MemberSyntaxProof.membersSubst]

theorem fieldsRename {beta : Type}  (types code t : OTerm alpha) (j : alpha → beta) :
    (fields types code t).relabel j = fields (types.relabel j) (code.relabel j) (t.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields types code t).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness  (types code : OTerm alpha) (ys : Fin 1 → OTerm alpha) :
    (matrix types code).subst (Sum.elim Term.var (fun i => emb (ys i))) = fields types code (ys 0) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem caseSubst {beta : Type}  (types code : OTerm alpha) (sub : alpha → OTerm beta) :
    (Targets.bottomCase types code).subst (fun a => emb (sub a)) = Targets.bottomCase (types.subst sub) (code.subst sub) := by
  change (InternalFiniteBlocks.block (matrix types code)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix (types.subst sub) (code.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem caseRename {beta : Type}  (types code : OTerm alpha) (j : alpha → beta) :
    (Targets.bottomCase types code).relabel j = Targets.bottomCase (types.relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.bottomCase types code).subst (fun a => emb (.var (j a))) = _
  rw [caseSubst]
  simp only [← termRelabelAsSubst]

theorem introduce  (types code : OTerm alpha) (ys : Fin 1 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields types code (ys 0)))) :
    Nonempty (Derivation body Delta (Targets.bottomCase types code)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix types code)))
  apply InternalFiniteBlocksProof.introduction body alpha 1 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases  (types code : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Targets.bottomCase types code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 1 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields (types.relabel j) (code.relabel j) (ys 0))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 1 Delta (matrix types code) psi hf
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let Theta := matrix types code :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 1) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.BottomSyntaxProof
