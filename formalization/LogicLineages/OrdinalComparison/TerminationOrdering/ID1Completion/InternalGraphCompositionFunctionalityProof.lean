module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalGraphCompositionSyntaxProof InternalGraphCompositionIntroductionProof InternalGraphCompositionEqualityProof
open InternalFiniteBlocksProof InternalDerivationRenamingProof InternalPositiveUnfoldingSupportProof
open InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)

theorem renameInto {body : Positive (Fin 1)} {α β : Type} {Gamma : List (Formula α)} {phi : Formula α}
    (h : Nonempty (Derivation body Gamma phi)) (f : α → β) (Delta : List (Formula β))
    (hi : ∀ p ∈ Gamma, p.relabel f ∈ Delta) : Nonempty (Derivation body Delta (phi.relabel f)) := by
  obtain ⟨d⟩ := h
  obtain ⟨e⟩ := renameDerivation d β f
  apply Nonempty.intro
  apply Derivation.weakening ?_ e
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hi q hq

theorem equalityRename {α β : Type} (out other : OTerm α) (f : α → β) :
    (arithmeticEmbedding.onFormula (out.equal other)).relabel f =
      arithmeticEmbedding.onFormula ((out.relabel f).equal (other.relabel f)) := by
  rw [onEquality,onEquality]
  change (eqn out other).relabel f = eqn (out.relabel f) (other.relabel f)
  exact eqnRelabel out other f

/-- Eliminate exactly the original intermediate block, exposing original
component graph derivations in its fresh-variable branch. -/
theorem compositionCases {body : Positive (Fin 1)} {m n : Nat} {α : Type}
    (Gamma : List (Formula α)) (f : OFormula (Fin (n+1))) (g : Fin n → OFormula (Fin (m+1)))
    (out : OTerm α) (xs : Fin m → OTerm α) (psi : Formula α)
    (d : Nonempty (Derivation body Gamma (graph (OrdinaryArithmetic.compositionGraph f g) out xs)))
    (h : ∀ (β : Type) (j : α → β) (ys : Fin n → OTerm β) (Delta : List (Formula β)),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph f (out.relabel j) ys)) →
      (∀ i, Nonempty (Derivation body Delta (graph (g i) (ys i) (fun a => (xs a).relabel j)))) →
      Nonempty (Derivation body Delta (psi.relabel j))) : Nonempty (Derivation body Gamma psi) := by
  apply actualOriginalCompositionElimination body m n α Gamma f g out xs psi d
  let M := arithmeticEmbedding.onFormula (matrix f g out xs)
  let Delta := M :: Gamma.map (fun p => p.relabel Sum.inl)
  apply h (α ⊕ Fin n) Sum.inl (fun i => .var (.inr i)) Delta
  · intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · apply (actualOriginalFiniteConjunction body (α ⊕ Fin n) n Delta
      (fun i => OrdinaryArithmetic.applyGraph (g i) (.var (.inr i)) (fun a => (xs a).relabel Sum.inl))).mp
    exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩

theorem functionalApply {body : Positive (Fin 1)} {n : Nat} {α : Type}
    (f : OFormula (Fin (n+1))) (hf : Functional body f) (Gamma : List (Formula α))
    (out other : OTerm α) (xs : Fin n → OTerm α)
    (d : Nonempty (Derivation body Gamma (graph f out xs)))
    (e : Nonempty (Derivation body Gamma (graph f other xs))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (out.equal other))) := by
  obtain ⟨r⟩ := hf α out other xs
  obtain ⟨d⟩ := d
  obtain ⟨e⟩ := e
  exact ⟨Derivation.implicationElimination (weakenClosed r Gamma) (Derivation.conjunctionIntroduction d e)⟩

theorem compositionFunctionalCore {body : Positive (Fin 1)} {m n : Nat} {α : Type}
    (f : OFormula (Fin (n+1))) (g : Fin n → OFormula (Fin (m+1)))
    (hf : Functional body f) (hg : ∀ i, Functional body (g i))
    (Gamma : List (Formula α)) (out other : OTerm α) (xs : Fin m → OTerm α)
    (d : Nonempty (Derivation body Gamma (graph (OrdinaryArithmetic.compositionGraph f g) out xs)))
    (e : Nonempty (Derivation body Gamma (graph (OrdinaryArithmetic.compositionGraph f g) other xs))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (out.equal other))) := by
  apply compositionCases Gamma f g out xs _ d
  intro β j ys Delta hi df dg
  rw [equalityRename]
  have e' := renameInto e j Delta hi
  rw [graphRename] at e'
  apply compositionCases Delta f g (other.relabel j) (fun a => (xs a).relabel j) _ e'
  intro γ l zs Theta hl ef eg
  rw [equalityRename]
  have df' := renameInto df l Theta hl
  rw [graphRename] at df'
  have dg' (i : Fin n) := renameInto (dg i) l Theta hl
  have heq (i : Fin n) : Nonempty (Derivation body Theta
      (arithmeticEmbedding.onFormula (((ys i).relabel l).equal (zs i)))) := by
    apply functionalApply (g i) (hg i) Theta ((ys i).relabel l) (zs i)
      (fun a => ((xs a).relabel j).relabel l)
    · simpa only [graphRename] using dg' i
    · exact eg i
  have dt := graphInputTransport body γ n Theta f ((out.relabel j).relabel l)
    (fun i => (ys i).relabel l) zs heq df'
  exact functionalApply f hf Theta ((out.relabel j).relabel l) ((other.relabel j).relabel l) zs dt ef

theorem actualOriginalCompositionFunctionality : InternalGraphCompositionTargets.ActualOriginalCompositionFunctionality := by
  intro body m n f g hf hg α out other xs
  let A := graph (OrdinaryArithmetic.compositionGraph f g) out xs ⊓
    graph (OrdinaryArithmetic.compositionGraph f g) other xs
  obtain ⟨d⟩ := compositionFunctionalCore f g hf hg [A] out other xs
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
