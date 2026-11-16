module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinarySyntaxProof
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
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def fields (n : Nat) (cons : Bool) (left right out : OTerm alpha) (ys : Fin 7 → OTerm alpha) : Formula alpha :=
  graph1 (OriginalCodeBoundsRecursion.bounds n) (ys 0) left ⊓
  graph2 InternalPairing.pairing (ys 0) (ys 1) (ys 2) ⊓
  graph1 (OriginalCodeBoundsRecursion.bounds n) (ys 3) right ⊓
  graph2 InternalPairing.pairing (ys 3) (ys 4) (ys 5) ⊓
  graph2 OriginalBoundsRecombination.maximum (ys 6) (ys 2) (ys 5) ⊓
  graph2 InternalPairing.pairing out
    (if cons then OrdinaryArithmetic.addTerm (ys 1) (ys 4)
     else suc (OrdinaryArithmetic.addTerm (ys 1) (ys 4))) (ys 6)
def matrix (n : Nat) (cons : Bool) (left right out : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  fields n cons (left.relabel Sum.inl) (right.relabel Sum.inl) (out.relabel Sum.inl) (fun i => .var (.inr i))
def block (n : Nat) (cons : Bool) (left right out : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (matrix n cons left right out)

theorem fieldsSubst {beta : Type} (n : Nat) (cons : Bool) (left right out : OTerm alpha)
    (ys : Fin 7 → OTerm alpha) (sub : alpha → OTerm beta) :
    (fields n cons left right out ys).subst (fun a => emb (sub a)) =
      fields n cons (left.subst sub) (right.subst sub) (out.subst sub) (fun i => (ys i).subst sub) := by
  cases cons <;> simp only [fields,conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,
    consTermSubst,emptySubst,sucSubst,addSubst,if_true,if_false]

theorem fieldsRename {beta : Type} (n : Nat) (cons : Bool) (left right out : OTerm alpha)
    (ys : Fin 7 → OTerm alpha) (j : alpha → beta) :
    (fields n cons left right out ys).relabel j =
      fields n cons (left.relabel j) (right.relabel j) (out.relabel j) (fun i => (ys i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n cons left right out ys).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (cons : Bool) (left right out : OTerm alpha) (ys : Fin 7 → OTerm alpha) :
    (matrix n cons left right out).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      fields n cons left right out ys := by
  have he : Sum.elim Term.var (fun i => emb (ys i)) = (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he,fieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]

theorem blockSubst {beta : Type} (n : Nat) (cons : Bool) (left right out : OTerm alpha) (sub : alpha → OTerm beta) :
    (block n cons left right out).subst (fun a => emb (sub a)) =
      block n cons (left.subst sub) (right.subst sub) (out.subst sub) := by
  unfold block matrix
  rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding,fieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem blockRename {beta : Type} (n : Nat) (cons : Bool) (left right out : OTerm alpha) (j : alpha → beta) :
    (block n cons left right out).relabel j = block n cons (left.relabel j) (right.relabel j) (out.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (block n cons left right out).subst (fun a => emb (.var (j a))) = _
  rw [blockSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (n : Nat) (cons : Bool) (left right out : OTerm alpha) (ys : Fin 7 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n cons left right out ys))) :
    Nonempty (Derivation body Delta (block n cons left right out)) := by
  apply InternalFiniteBlocksProof.introduction body alpha 7 Delta _ (fun i => emb (ys i))
  rw [matrixWitness]
  exact hf

theorem cases (n : Nat) (cons : Bool) (left right out : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (block n cons left right out)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (ys : Fin 7 → OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (fields n cons (left.relabel j) (right.relabel j) (out.relabel j) ys)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply InternalFiniteBlocksProof.elimination body alpha 7 Delta (matrix n cons left right out) psi hf
  let j : alpha → alpha ⊕ Fin 7 := Sum.inl
  let Theta := matrix n cons left right out :: Delta.map (fun q => q.relabel j)
  exact next (alpha ⊕ Fin 7) j Theta (fun i => .var (.inr i))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinarySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinarySyntaxProof
