module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinarySyntaxProof
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

def fields (n : Nat) (left right out dl dr maximum : OTerm alpha) : Formula alpha := graph1 (depth n) dl left ⊓ graph1 (depth n) dr right ⊓ graph2 OriginalBoundsRecombination.maximum maximum dl dr ⊓ eqn out (suc maximum)
def matrix (n : Nat) (left right out : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  fields n (left.relabel Sum.inl) (right.relabel Sum.inl) (out.relabel Sum.inl) (.var (.inr (0 : Fin 3))) (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3)))
def block (n : Nat) (left right out : OTerm alpha) : Formula alpha := InternalFiniteBlocks.block (matrix n left right out)

theorem fieldsSubst {beta : Type} (n : Nat) (left right out dl dr maximum : OTerm alpha) (sub : alpha → OTerm beta) :
    (fields n left right out dl dr maximum).subst (fun a => emb (sub a)) = fields n (left.subst sub) (right.subst sub) (out.subst sub) (dl.subst sub) (dr.subst sub) (maximum.subst sub) := by
  simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,eqnSubst,sucSubst]

theorem fieldsRename {beta : Type} (n : Nat) (left right out dl dr maximum : OTerm alpha) (j : alpha → beta) :
    (fields n left right out dl dr maximum).relabel j = fields n (left.relabel j) (right.relabel j) (out.relabel j) (dl.relabel j) (dr.relabel j) (maximum.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n left right out dl dr maximum).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (left right out : OTerm alpha) (ys : Fin 3 → OTerm alpha) :
    (matrix n left right out).subst (Sum.elim Term.var (fun i => emb (ys i))) = fields n left right out (ys 0) (ys 1) (ys 2) := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem blockSubst {beta : Type} (n : Nat) (left right out : OTerm alpha) (sub : alpha → OTerm beta) :
    (block n left right out).subst (fun a => emb (sub a)) = block n (left.subst sub) (right.subst sub) (out.subst sub) := by
  unfold block matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem blockRename {beta : Type} (n : Nat) (left right out : OTerm alpha) (j : alpha → beta) :
    (block n left right out).relabel j = block n (left.relabel j) (right.relabel j) (out.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (block n left right out).subst (fun a => emb (.var (j a))) = _
  rw [blockSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (left right out : OTerm alpha) (ys : Fin 3 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n left right out (ys 0) (ys 1) (ys 2)))) :
    Nonempty (Derivation body Delta (block n left right out)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 3 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases (n : Nat) (left right out : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (block n left right out)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 3 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields n (left.relabel j) (right.relabel j) (out.relabel j) (ys 0) (ys 1) (ys 2))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 3 Delta (matrix n left right out) psi hf
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let Theta := matrix n left right out :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 3) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinarySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinarySyntaxProof
