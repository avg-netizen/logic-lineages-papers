module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldIndexProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst)
open ID1Completion.InternalBinderTransportProof
open ID1Completion.InternalBinderTransportSyntaxProof (onTermRelabel)
open ID1Completion.InternalDerivationRenamingSyntaxProof (instantiateRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open NumberedWindowInternalSparseFieldInductionTargets NumberedWindowInternalSparseFieldExistentialProof

theorem atCodeRename {α β : Type} (θ : Formula (α ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (atCode θ n).relabel j = atCode (θ.relabel (Sum.map j id)) (n.relabel j) := by
  unfold atCode
  rw [instantiateRename,← onTermRelabel]

private theorem atIndexRename {α β : Type} (θ : Formula (α ⊕ Fin 1))
    (i : Fin 3) (j : α → β) :
    (atIndex θ i).relabel (Sum.map j id) =
      atIndex (θ.relabel (Sum.map j id)) i := by
  unfold atIndex
  rw [formulaRelabelComposition,formulaRelabelComposition]
  congr 1
  funext a
  cases a <;> rfl

private theorem allBlockRename {α β : Type} {k : Nat} (φ : Formula (α ⊕ Fin k))
    (j : α → β) : (allBlock φ).relabel j = allBlock (φ.relabel (Sum.map j id)) := by
  rw [formulaRelabelAsSubst,allBlockSubst,formulaRelabelAsSubst]
  congr 2
  funext a
  cases a <;> rfl

private theorem consBodyRename {α β : Type} (θ : Formula (α ⊕ Fin 1))
    (j : α → β) :
    (consBody θ).relabel (Sum.map j id) = consBody (θ.relabel (Sum.map j id)) := by
  change ((consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).relabel
    (Sum.map j id)).imp (((atIndex θ 2).relabel (Sum.map j id)).imp
      ((atIndex θ 0).relabel (Sum.map j id))) = _
  rw [consGraphRename,atIndexRename,atIndexRename]
  rfl

theorem consRuleRename {α β : Type} (θ : Formula (α ⊕ Fin 1))
    (j : α → β) : (consRule θ).relabel j = consRule (θ.relabel (Sum.map j id)) := by
  rw [consRule,allBlockRename,consBodyRename]
  rfl

private theorem atIndexWitness {α : Type} (θ : Formula (α ⊕ Fin 1))
    (i : Fin 3) (ts : Fin 3 → OTerm α) :
    (atIndex θ i).subst (Sum.elim Term.var (fun k => emb (ts k))) = atCode θ (ts i) := by
  rw [atIndex,actualRelabelSubstitution]
  unfold atCode instantiate
  congr 1
  funext a
  cases a <;> rfl

private def codes {α : Type} (n h t : OTerm α) : Fin 3 → OTerm α :=
  Fin.cases n (Fin.cases h (fun _ => t))

private theorem consBodyWitness {α : Type} (θ : Formula (α ⊕ Fin 1)) (n h t : OTerm α) :
    (consBody θ).subst (Sum.elim Term.var (fun i => emb (codes n h t i))) =
      (consGraph n h t).imp ((atCode θ t).imp (atCode θ n)) := by
  let ts := codes n h t
  have he : (Sum.elim Term.var (fun i => emb (ts i))) =
      (fun x => emb (Sum.elim Term.var ts x)) := by
    funext x
    cases x <;> rfl
  have graphAt : (consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).subst
      (Sum.elim Term.var (fun i => emb (ts i))) = consGraph n h t := by
    rw [he,consGraphSubst]
    rfl
  change ((consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).subst
      (Sum.elim Term.var (fun i => emb (ts i)))).imp
      (((atIndex θ 2).subst (Sum.elim Term.var (fun i => emb (ts i)))).imp
        ((atIndex θ 0).subst (Sum.elim Term.var (fun i => emb (ts i))))) = _
  rw [graphAt,atIndexWitness,atIndexWitness]
  rfl

theorem consApply {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (θ : Formula (α ⊕ Fin 1)) (n h t : OTerm α)
    (rule : Nonempty (Derivation body Γ (consRule θ)))
    (cons : Nonempty (Derivation body Γ (consGraph n h t)))
    (tail : Nonempty (Derivation body Γ (atCode θ t))) :
    Nonempty (Derivation body Γ (atCode θ n)) := by
  obtain ⟨rule⟩ := actualFiniteUniversalElimination body α 3 Γ (consBody θ) (fun i => emb (codes n h t i)) rule
  rw [consBodyWitness] at rule
  obtain ⟨cons⟩ := cons
  obtain ⟨tail⟩ := tail
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination rule cons) tail⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldIndexProof
