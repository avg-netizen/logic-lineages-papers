module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalClosedPrograms InternalListCodec InternalListInduction
open InternalTagArithmeticSyntaxProof InternalBinderTransportSyntaxProof
open InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalDerivationRenamingSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalSourceIntroductionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalListCodecSupportProof InternalRecursionGraphStepSyntaxProof
open InternalAdditionLawsProof InternalClosedProgramsBindingProof

theorem atCodeRename {α β : Type} (theta : Formula (α ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (atCode theta n).relabel j =
      atCode (theta.relabel (Sum.map j id)) (n.relabel j) := by
  unfold atCode
  rw [instantiateRename, ← onTermRelabel]

theorem atIndexRename {α β : Type} (theta : Formula (α ⊕ Fin 1))
    (i : Fin 3) (j : α → β) :
    (atIndex theta i).relabel (Sum.map j id) =
      atIndex (theta.relabel (Sum.map j id)) i := by
  unfold atIndex
  rw [formulaRelabelComposition, formulaRelabelComposition]
  congr 1
  funext a
  cases a <;> rfl

theorem allBlockRename {α β : Type} {k : Nat} (phi : Formula (α ⊕ Fin k))
    (j : α → β) :
    (allBlock phi).relabel j = allBlock (phi.relabel (Sum.map j id)) := by
  rw [formulaRelabelAsSubst, allBlockSubst, formulaRelabelAsSubst]
  congr 2
  funext a
  cases a <;> rfl

theorem constructorBodyRename {α β : Type} (theta : Formula (α ⊕ Fin 1))
    (j : α → β) :
    (constructorBody theta).relabel (Sum.map j id) =
      constructorBody (theta.relabel (Sum.map j id)) := by
  change ((consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).relabel
    (Sum.map j id)).imp (((atIndex theta 2).relabel (Sum.map j id)).imp
      ((atIndex theta 0).relabel (Sum.map j id))) = _
  rw [consGraphRename, atIndexRename, atIndexRename]
  rfl

theorem constructorsRename {α β : Type} (theta : Formula (α ⊕ Fin 1))
    (j : α → β) :
    (constructors theta).relabel j = constructors (theta.relabel (Sum.map j id)) := by
  rw [constructors, allBlockRename, constructorBodyRename]
  rfl

theorem premisesRename {α β : Type} (theta : Formula (α ⊕ Fin 1))
    (j : α → β) :
    (premises theta).relabel j = premises (theta.relabel (Sum.map j id)) := by
  change ((atCode theta z).relabel j) ⊓ ((constructors theta).relabel j) = _
  rw [atCodeRename, zRelabel, constructorsRename]
  rfl

theorem atIndexWitness {α : Type} (theta : Formula (α ⊕ Fin 1))
    (i : Fin 3) (ts : Fin 3 → OTerm α) :
    (atIndex theta i).subst (Sum.elim Term.var (fun k => emb (ts k))) =
      atCode theta (ts i) := by
  rw [atIndex, actualRelabelSubstitution]
  unfold atCode instantiate
  congr 1
  funext a
  cases a <;> rfl

def codeValues {α : Type} (n h t : OTerm α) : Fin 3 → OTerm α :=
  Fin.cases n (Fin.cases h (fun _ => t))

theorem constructorBodyWitness {α : Type} (theta : Formula (α ⊕ Fin 1))
    (n h t : OTerm α) :
    (constructorBody theta).subst
      (Sum.elim Term.var (fun i => emb (codeValues n h t i))) =
      (consGraph n h t).imp ((atCode theta t).imp (atCode theta n)) := by
  let ts := codeValues n h t
  have he : (Sum.elim Term.var (fun i => emb (ts i))) =
      (fun x => emb (Sum.elim Term.var ts x)) := by
    funext a
    cases a <;> rfl
  have hg : (consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).subst
      (Sum.elim Term.var (fun i => emb (ts i))) = consGraph n h t := by
    rw [he]
    change (InternalGraphComposition.graph (OrdinaryArithmetic.graphFormula consCode) _ _).subst _ = _
    rw [graphSubst]
    congr 1
    funext i
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.elim0 l) k) i <;> rfl
  change ((consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).subst
      (Sum.elim Term.var (fun i => emb (ts i)))).imp
      (((atIndex theta 2).subst (Sum.elim Term.var (fun i => emb (ts i)))).imp
        ((atIndex theta 0).subst (Sum.elim Term.var (fun i => emb (ts i))))) = _
  rw [hg, atIndexWitness, atIndexWitness]
  rfl

/-- Instantiate the actual three universal binders, in their original order. -/
theorem constructorApply {body : Positive (Fin 1)} {α : Type}
    {Gamma : List (Formula α)} (theta : Formula (α ⊕ Fin 1)) (n h t : OTerm α)
    (hs : Nonempty (Derivation body Gamma (constructors theta)))
    (hc : Nonempty (Derivation body Gamma (consGraph n h t)))
    (ht : Nonempty (Derivation body Gamma (atCode theta t))) :
    Nonempty (Derivation body Gamma (atCode theta n)) := by
  obtain ⟨hs⟩ := actualFiniteUniversalElimination body α 3 Gamma (constructorBody theta)
    (fun i => emb (codeValues n h t i)) hs
  rw [constructorBodyWitness] at hs
  obtain ⟨hc⟩ := hc
  obtain ⟨ht⟩ := ht
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination hs hc) ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
