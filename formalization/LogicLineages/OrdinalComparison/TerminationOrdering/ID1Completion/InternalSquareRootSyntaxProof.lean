module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalSquareRoot InternalSquareRootArithmetic
open InternalSquareRootArithmeticSupportProof InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalBinderTransportSyntaxProof InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalDerivationRenamingSyntaxProof InternalFiniteBlocksSubstitutionProof InternalCoprimeMultipleSyntaxProof

abbrev rootGraph {α : Type} (out n : OTerm α) : Formula α :=
  programGraph root out (Fin.cons n Fin.elim0)

@[simp] theorem rootGraphRename {α β : Type} (out n : OTerm α) (j : α → β) :
    (rootGraph out n).relabel j = rootGraph (out.relabel j) (n.relabel j) := by
  unfold rootGraph
  rw [programRename]
  congr 1
  funext i
  obtain rfl : i = 0 := Fin.eq_zero i
  rfl

@[simp] theorem rootGraphSubst {α β : Type} (out n : OTerm α) (ts : α → OTerm β) :
    (rootGraph out n).subst (fun a => emb (ts a)) = rootGraph (out.subst ts) (n.subst ts) := by
  unfold rootGraph programGraph
  rw [graphSubst]
  congr 1
  funext i
  obtain rfl : i = 0 := Fin.eq_zero i
  rfl

@[simp] theorem rootGraphInstantiate {α : Type} (out n : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (rootGraph out n) (emb t) = rootGraph (out.subst (bindTerm t)) (n.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rootGraphSubst]

/-- An object-language witness carries both the literal program graph and
its interval. No meta-level natural number is selected. -/
def certified {α : Type} (n : OTerm α) : Formula α :=
  existsOne (rootGraph (.var (.inr 0)) (n.relabel Sum.inl) ⊓
    interval (.var (.inr 0)) (n.relabel Sum.inl))

@[simp] theorem certifiedRename {α β : Type} (n : OTerm α) (j : α → β) :
    (certified n).relabel j = certified (n.relabel j) := by
  unfold certified
  rw [existsRename]
  change existsOne ((rootGraph (.var (.inr 0)) (n.relabel Sum.inl)).relabel (Sum.map j id) ⊓
    (interval (.var (.inr 0)) (n.relabel Sum.inl)).relabel (Sum.map j id)) = _
  simp only [rootGraphRename,intervalRename,Term.relabel,Term.relabel_relabel]
  rfl

@[simp] theorem certifiedSubst {α β : Type} (n : OTerm α) (ts : α → OTerm β) :
    (certified n).subst (fun a => emb (ts a)) = certified (n.subst ts) := by
  unfold certified
  rw [existsSubst]
  let lift : α ⊕ Fin 1 → OTerm (β ⊕ Fin 1) :=
    Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))
  have he : Sum.elim (fun a => (emb (ts a)).relabel Sum.inl)
      (fun i : Fin 1 => (Term.var (.inr i) : InternalCalculus.Term (β ⊕ Fin 1))) =
      fun a => emb (lift a) := by
    funext a
    cases a with
    | inl a => exact (onTermRelabel arithmeticEmbedding Sum.inl (ts a)).symm
    | inr i => rfl
  have ht : (n.relabel Sum.inl).subst lift = (n.subst ts).relabel Sum.inl := by
    rw [termRelabelSubst,termSubstRelabel]
    rfl
  rw [he,infSubst,rootGraphSubst,intervalSubst,ht]
  rfl

@[simp] theorem certifiedInstantiate {α : Type} (n : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (certified n) (emb t) = certified (n.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,certifiedSubst]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem certifiedIntroduction (n out : OTerm α)
    (hg : Nonempty (Derivation body Gamma (rootGraph out n)))
    (hi : Nonempty (Derivation body Gamma (interval out n))) :
    Nonempty (Derivation body Gamma (certified n)) := by
  obtain ⟨hg⟩ := hg
  obtain ⟨hi⟩ := hi
  unfold certified
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  simp only [infInstantiate,rootGraphInstantiate,intervalInstantiate,varBind,liftBind]
  exact Derivation.conjunctionIntroduction hg hi

theorem certifiedCases (Gamma : List (Formula α)) (n : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (certified n)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (rootGraph out (n.relabel j))) →
      Nonempty (Derivation body Delta (interval out (n.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let phi := rootGraph v (n.relabel Sum.inl) ⊓ interval v (n.relabel Sum.inl)
  have e := k (α ⊕ Fin 1) Sum.inl (phi :: Gamma.map weaken) v
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨e⟩ := e
  exact ⟨Derivation.existentialElimination h e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootSyntaxProof
