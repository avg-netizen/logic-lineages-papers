module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
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

def fields (n : Nat) (labels heads types tupleBound prior code k encoded raw t base tuple extra len : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess k (suc labels) ⊓ graph2 contains (numeral 1) heads encoded ⊓ graph1 (OriginalEncodedHeadConversion.convert n) raw encoded ⊓ graph2 contains (numeral 1) types t ⊓ graph2 contains (numeral 1) prior base ⊓ OriginalContextInsertion.lengthGraph len tuple ⊓ InternalLessThan.strictLess len (suc tupleBound) ⊓ OriginalTypeListsMembership.Targets.allMembers tuple types ⊓ graph2 contains (numeral 1) prior extra ⊓ programGraph OriginalRawSyntaxTransport.numberedConstructor code ![k,raw,t,base,tuple,extra]
def matrix (n : Nat) (labels heads types tupleBound prior code : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
  fields n (labels.relabel Sum.inl) (heads.relabel Sum.inl) (types.relabel Sum.inl) (tupleBound.relabel Sum.inl) (prior.relabel Sum.inl) (code.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))

theorem fieldsSubst {beta : Type} (n : Nat) (labels heads types tupleBound prior code k encoded raw t base tuple extra len : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields n labels heads types tupleBound prior code k encoded raw t base tuple extra len).subst (fun a => emb (sub a)) = fields n (labels.subst sub) (heads.subst sub) (types.subst sub) (tupleBound.subst sub) (prior.subst sub) (code.subst sub) (k.subst sub) (encoded.subst sub) (raw.subst sub) (t.subst sub) (base.subst sub) (tuple.subst sub) (extra.subst sub) (len.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,numeral,zSubst,sucSubst,InternalLessThan.strictLess,
    InternalQuotientComparisonSyntaxProof.orderSubst,OriginalContextInsertionSyntaxProof.lengthSubst,
    OriginalTypeListsMembership.MemberSyntaxProof.membersSubst]
  have hxs : (fun i : Fin 6 => (![k,raw,t,base,tuple,extra] i).subst sub) = ![k.subst sub,raw.subst sub,t.subst sub,base.subst sub,tuple.subst sub,extra.subst sub] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs]

theorem fieldsRename {beta : Type} (n : Nat) (labels heads types tupleBound prior code k encoded raw t base tuple extra len : OTerm alpha) (j : alpha → beta) :
    (fields n labels heads types tupleBound prior code k encoded raw t base tuple extra len).relabel j = fields n (labels.relabel j) (heads.relabel j) (types.relabel j) (tupleBound.relabel j) (prior.relabel j) (code.relabel j) (k.relabel j) (encoded.relabel j) (raw.relabel j) (t.relabel j) (base.relabel j) (tuple.relabel j) (extra.relabel j) (len.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n labels heads types tupleBound prior code k encoded raw t base tuple extra len).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (labels heads types tupleBound prior code : OTerm alpha) (ys : Fin 8 → OTerm alpha) :
    (matrix n labels heads types tupleBound prior code).subst (Sum.elim Term.var (fun i => emb (ys i))) = fields n labels heads types tupleBound prior code (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem caseSubst {beta : Type} (n : Nat) (labels heads types tupleBound prior code : OTerm alpha) (sub : alpha → OTerm beta) :
    (Targets.numberedCase n labels heads types tupleBound prior code).subst (fun a => emb (sub a)) = Targets.numberedCase n (labels.subst sub) (heads.subst sub) (types.subst sub) (tupleBound.subst sub) (prior.subst sub) (code.subst sub) := by
  change (InternalFiniteBlocks.block (matrix n labels heads types tupleBound prior code)).subst (fun a => emb (sub a)) =
    InternalFiniteBlocks.block (matrix n (labels.subst sub) (heads.subst sub) (types.subst sub) (tupleBound.subst sub) (prior.subst sub) (code.subst sub))
  unfold matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem caseRename {beta : Type} (n : Nat) (labels heads types tupleBound prior code : OTerm alpha) (j : alpha → beta) :
    (Targets.numberedCase n labels heads types tupleBound prior code).relabel j = Targets.numberedCase n (labels.relabel j) (heads.relabel j) (types.relabel j) (tupleBound.relabel j) (prior.relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Targets.numberedCase n labels heads types tupleBound prior code).subst (fun a => emb (.var (j a))) = _
  rw [caseSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (labels heads types tupleBound prior code : OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n labels heads types tupleBound prior code (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7)))) :
    Nonempty (Derivation body Delta (Targets.numberedCase n labels heads types tupleBound prior code)) := by
  change Nonempty (Derivation body Delta (InternalFiniteBlocks.block (matrix n labels heads types tupleBound prior code)))
  apply InternalFiniteBlocksProof.introduction body alpha 8 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases (n : Nat) (labels heads types tupleBound prior code : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Targets.numberedCase n labels heads types tupleBound prior code)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 8 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields n (labels.relabel j) (heads.relabel j) (types.relabel j) (tupleBound.relabel j) (prior.relabel j) (code.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 8 Delta (matrix n labels heads types tupleBound prior code) psi hf
  let j : alpha → alpha ⊕ Fin 8 := Sum.inl
  let Theta := matrix n labels heads types tupleBound prior code :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 8) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationLayerFields.NumberedSyntaxProof
