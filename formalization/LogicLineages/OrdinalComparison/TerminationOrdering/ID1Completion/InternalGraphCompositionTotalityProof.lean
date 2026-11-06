module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionIntroductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof InternalGraphCompositionSyntaxProof
open InternalGraphCompositionIntroductionProof InternalDerivationRenamingProof
open InternalDerivationRenamingSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalFiniteBlocksSubstitutionProof

/-- Output existence commutes with free renaming. Its witness remains bound. -/
theorem graphExistsRename {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (xs : Fin n → OTerm α) (h : α → β) :
    (existsOne (graph f (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl))).relabel h =
    existsOne (graph f (.var (.inr (0 : Fin 1)))
      (fun i => ((xs i).relabel h).relabel Sum.inl)) := by
  simp only [existsRename,graphRename,Term.relabel,Term.relabel_relabel] <;> rfl

/-- A finite sequence of original existential eliminations supplies ordinary
term witnesses to a continuation. The continuation transports every old
hypothesis explicitly; no semantic witness is selected. -/
theorem supplyOutputs (body : Positive (Fin 1)) (m n : Nat) :
    ∀ (g : Fin n → OFormula (Fin (m+1))),
    (∀ i, Total body (g i)) →
    ∀ (α : Type) (Gamma : List (Formula α)) (xs : Fin m → OTerm α) (psi : Formula α),
    (∀ (β : Type) (h : α → β) (Delta : List (Formula β)) (ys : Fin n → OTerm β),
      (∀ p, p ∈ Gamma → p.relabel h ∈ Delta) →
      (∀ i, Nonempty (Derivation body Delta
        (graph (g i) (ys i) (fun j => (xs j).relabel h)))) →
      Nonempty (Derivation body Delta (psi.relabel h))) →
    Nonempty (Derivation body Gamma psi) := by
  induction n with
  | zero =>
    intro g hg α Gamma xs psi k
    have hGamma : ∀ p, p ∈ Gamma → p.relabel id ∈ Gamma := by
      intro p hp
      simpa only [renameIdentity] using hp
    have he := k α id Gamma (fun i => Fin.elim0 i) hGamma
      (fun i => Fin.elim0 i)
    simpa only [renameIdentity] using he
  | succ n ih =>
    intro g hg α Gamma xs psi k
    let phi : Formula (α ⊕ Fin 1) :=
      graph (g 0) (.var (.inr (0 : Fin 1))) (fun j => (xs j).relabel Sum.inl)
    let Delta : List (Formula (α ⊕ Fin 1)) := phi :: Gamma.map weaken
    obtain ⟨d⟩ := hg 0 α xs
    have he : Nonempty (Derivation body Delta (weaken psi)) := by
      apply ih (fun i => g i.succ) (fun i => hg i.succ) (α ⊕ Fin 1) Delta
        (fun j => (xs j).relabel Sum.inl) (weaken psi)
      intro β h Theta ys hDelta hy
      let zs : Fin (n+1) → OTerm β :=
        Fin.cases (.var (h (.inr (0 : Fin 1)))) ys
      have hGamma : ∀ p, p ∈ Gamma → p.relabel (h ∘ Sum.inl) ∈ Theta := by
        intro p hp
        have hm : weaken p ∈ Delta :=
          List.mem_cons_of_mem phi (List.mem_map.mpr ⟨p,hp,rfl⟩)
        have hh := hDelta (weaken p) hm
        simpa only [weaken,formulaRelabelComposition] using hh
      have hz : ∀ i, Nonempty (Derivation body Theta
          (graph (g i) (zs i) (fun j => (xs j).relabel (h ∘ Sum.inl)))) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · have hp := hDelta phi (show phi ∈ Delta from List.mem_cons_self)
          have hh : graph (g 0) (zs 0)
              (fun j => (xs j).relabel (h ∘ Sum.inl)) ∈ Theta := by
            simpa only [phi,zs,graphRename,Term.relabel,Term.relabel_relabel,
              Fin.cases_zero] using hp
          exact ⟨Derivation.hypothesis hh⟩
        · simpa only [zs,Fin.cases_succ,Term.relabel_relabel] using hy j
      have hh := k β (h ∘ Sum.inl) Theta zs hGamma hz
      simpa only [weaken,formulaRelabelComposition] using hh
    obtain ⟨e⟩ := he
    exact ⟨Derivation.existentialElimination (weakenClosed d Gamma) e⟩

/-- Explicit component totality trees close under the original composition
constructor. Every output and intermediate value is introduced or eliminated
using the original finitary calculus. -/
theorem actualOriginalCompositionTotality :
    InternalGraphCompositionTargets.ActualOriginalCompositionTotality := by
  intro body m n f g hf hg α xs
  let psi : Formula α := existsOne
    (graph (OrdinaryArithmetic.compositionGraph f g) (.var (.inr (0 : Fin 1)))
      (fun j => (xs j).relabel Sum.inl))
  change Nonempty (Derivation body [] psi)
  apply supplyOutputs body m n g hg α [] xs psi
  intro β h Delta ys _ hys
  let phi : Formula (β ⊕ Fin 1) :=
    graph f (.var (.inr (0 : Fin 1))) (fun i => (ys i).relabel Sum.inl)
  let Theta : List (Formula (β ⊕ Fin 1)) := phi :: Delta.map weaken
  obtain ⟨df⟩ := hf β ys
  have hgs : ∀ i, Nonempty (Derivation body Theta
      (graph (g i) ((ys i).relabel Sum.inl)
        (fun j => ((xs j).relabel h).relabel Sum.inl))) := by
    intro i
    obtain ⟨di⟩ := hys i
    obtain ⟨di'⟩ := renameDerivation di (β ⊕ Fin 1) Sum.inl
    rw [graphRename] at di'
    exact ⟨Derivation.weakening (fun p hp => List.mem_cons_of_mem phi hp) di'⟩
  have hc := actualOriginalCompositionIntroduction body m n (β ⊕ Fin 1) Theta f g
    (.var (.inr (0 : Fin 1))) (fun j => ((xs j).relabel h).relabel Sum.inl)
    (fun i => (ys i).relabel Sum.inl)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ hgs
  obtain ⟨dc⟩ := hc
  have ho : Nonempty (Derivation body Theta (weaken (psi.relabel h))) := by
    simp only [psi,weaken,graphExistsRename]
    apply Nonempty.intro
    apply Derivation.existentialIntroduction
      (arithmeticEmbedding.onTerm (.var (.inr (0 : Fin 1)) : OTerm (β ⊕ Fin 1)))
    rw [graphOutputInstantiate]
    exact dc
  obtain ⟨dout⟩ := ho
  exact ⟨Derivation.existentialElimination (weakenClosed df Delta) dout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
