module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinarySyntaxProof
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

def fields (n : Nat) (heads prior code encoded raw base : OTerm alpha) : Formula alpha :=
  graph2 contains (numeral 1) heads encoded ⊓ graph1 (OriginalEncodedHeadConversion.convert n) raw encoded ⊓ graph2 contains (numeral 1) prior base ⊓ graph2 OriginalRawSyntaxTransport.ordinaryConstructor code raw base
def matrix (n : Nat) (heads prior code : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  fields n (heads.relabel Sum.inl) (prior.relabel Sum.inl) (code.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

theorem fieldsSubst {beta : Type} (n : Nat) (heads prior code encoded raw base : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields n heads prior code encoded raw base).subst (fun a => emb (sub a)) = fields n (heads.subst sub) (prior.subst sub) (code.subst sub) (encoded.subst sub) (raw.subst sub) (base.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,numeral,zSubst,sucSubst,InternalLessThan.strictLess,
    InternalQuotientComparisonSyntaxProof.orderSubst,OriginalContextInsertionSyntaxProof.lengthSubst,
    OriginalTypeListsMembership.MemberSyntaxProof.membersSubst]

theorem fieldsRename {beta : Type} (n : Nat) (heads prior code encoded raw base : OTerm alpha) (j : alpha → beta) :
    (fields n heads prior code encoded raw base).relabel j = fields n (heads.relabel j) (prior.relabel j) (code.relabel j) (encoded.relabel j) (raw.relabel j) (base.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n heads prior code encoded raw base).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (heads prior code : OTerm alpha) (ys : Fin 3 → OTerm alpha) :
    (matrix n heads prior code).subst (Sum.elim Term.var (fun i => emb (ys i))) = fields n heads prior code (ys 0) (ys 1) (ys 2) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem caseSubst {beta : Type} (n : Nat) (heads prior code : OTerm alpha) (sub : alpha → OTerm beta) :
    (Targets.ordinaryCase n heads prior code).subst (fun a => emb (sub a)) = Targets.ordinaryCase n (heads.subst sub) (prior.subst sub) (code.subst sub) := by
  change (InternalFiniteBlocks.block (matrix n heads prior code)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix n (heads.subst sub) (prior.subst sub) (code.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem caseRename {beta : Type} (n : Nat) (heads prior code : OTerm alpha) (j : alpha → beta) :
    (Targets.ordinaryCase n heads prior code).relabel j = Targets.ordinaryCase n (heads.relabel j) (prior.relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.ordinaryCase n heads prior code).subst (fun a => emb (.var (j a))) = _
  rw [caseSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (heads prior code : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n heads prior code (ys 0) (ys 1) (ys 2)))) :
    Nonempty (Derivation body Delta (Targets.ordinaryCase n heads prior code)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix n heads prior code)))
  apply InternalFiniteBlocksProof.introduction body alpha 3 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases (n : Nat) (heads prior code : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Targets.ordinaryCase n heads prior code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 3 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields n (heads.relabel j) (prior.relabel j) (code.relabel j) (ys 0) (ys 1) (ys 2))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Delta (matrix n heads prior code) psi hf
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let Theta := matrix n heads prior code :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 3) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinarySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.OrdinarySyntaxProof
