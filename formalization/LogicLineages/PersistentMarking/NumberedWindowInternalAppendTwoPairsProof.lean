module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAppendTwoPairsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev App (l r o : OTerm α) : Formula α := programGraph append o ![l,r]

/-- Choose the two exact original side appends and their exact ordered
join, retaining the actual physical first and second operands. -/
theorem exact_OriginalAppendTwoPairs (a b c d : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (l r joined : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (App (a.relabel j) (b.relabel j) l)) →
      Nonempty (Derivation B Δ (App (c.relabel j) (d.relabel j) r)) →
      Nonempty (Derivation B Δ (App l r joined)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases append ![a,b] goal
  intro β j Δ l keep al
  rw [binaryInputsRename] at al
  apply programCases append ![c.relabel j,d.relabel j] (goal.relabel j)
  intro γ k Ω r hold ar
  rw [binaryInputsRename] at ar
  apply programCases append ![l.relabel k,r] ((goal.relabel j).relabel k)
  intro δ q Xi out saved both
  rw [binaryInputsRename] at both
  let kj := k ∘ j
  let ρ := q ∘ kj
  have s := keepThrough j k keep hold
  have keep' := keepThrough kj q s saved
  have x := renamePair append l (a.relabel j) (b.relabel j) al (q ∘ k) (keepThrough k q hold saved)
  have y := renamePair append r ((c.relabel j).relabel k) ((d.relabel j).relabel k) ar q saved
  rw [formulaRelabelComposition j k goal,formulaRelabelComposition kj q goal]
  apply next δ ρ Xi ((l.relabel k).relabel q) (r.relabel q) out keep'
  · simpa only [App,ρ,kj,← Term.relabel_relabel,Function.comp_assoc] using x
  · simpa only [App,ρ,kj,← Term.relabel_relabel] using y
  · exact both

#print axioms exact_OriginalAppendTwoPairs
end LogicLineages.PersistentMarking.NumberedWindowInternalAppendTwoPairsProof
