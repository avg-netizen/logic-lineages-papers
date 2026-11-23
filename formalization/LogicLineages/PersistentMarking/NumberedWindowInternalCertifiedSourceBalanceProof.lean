module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSourceBalanceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverSymmetry exact_LiteralObserverTransitivity)
open NumberedWindowInternalCertifiedUnionStepProof (unionGraph)
open NumberedWindowInternalDirectSourcePartitionRawTargets (ParsedTriplet observePartition)
open NumberedWindowInternalDirectSourcePartitionRawProof (exact_OpenRawSourceDecode)
open NumberedWindowInternalDirectSourcePartitionAppendProof (exact_OpenSourcePartitionAppend)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser keepThrough)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev PC (raw s : OTerm α) : Formula α := unary parser (suc s) raw
abbrev A (l r v : OTerm α) : Formula α := programGraph append v ![l,r]
abbrev C (l r : OTerm α) : Formula α := programGraph permutation (suc z) ![l,r]

private theorem moveCount {β : Type} {Δ : List (Formula β)}
    (s r : OTerm α) (cmp : Nonempty (Derivation B Γ (C s r)))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (C (s.relabel j) (r.relabel j))) := by
  simpa only [C,sucRelabel,zRelabel] using renamePair permutation (suc z) s r cmp j keep

private theorem sameSource (raw seen whole localJoin certJoin : OTerm α)
    (p : Nonempty (Derivation B Γ (PC raw seen)))
    (q : Nonempty (Derivation B Γ (PC raw whole)))
    (s : Nonempty (Derivation B Γ (C seen localJoin)))
    (cert : Nonempty (Derivation B Γ (C whole certJoin))) :
    Nonempty (Derivation B Γ (C localJoin certJoin)) := by
  obtain ⟨e⟩ := valueUnique parser (suc seen) (suc whole) ![raw] p q
  have moved := headTransport permutation (suc z) seen whole ![localJoin] ⟨cancelSuc e⟩ s
  exact exact_LiteralObserverTransitivity localJoin whole certJoin
    (exact_LiteralObserverSymmetry whole localJoin moved) cert

/-- Align original union and certified source observations at their
same raw source. The kept split receives exact original left/right
parser outputs, actual their append, and the true duplicate-sensitive
comparison with the exact joined kept/removed tape. -/
theorem exact_OriginalCertifiedSourceBalance (a b u observed certJoin : OTerm α) (goal : Formula α)
    (union : Nonempty (Derivation B Γ (unionGraph permutation a b u)))
    (known : Nonempty (Derivation B Γ (PC u observed)))
    (cert : Nonempty (Derivation B Γ (C observed certJoin)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (l r joined : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (PC (a.relabel j) l)) →
      Nonempty (Derivation B Δ (PC (b.relabel j) r)) →
      Nonempty (Derivation B Δ (A l r joined)) →
      Nonempty (Derivation B Δ (C joined (certJoin.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply exact_OpenRawSourceDecode (observePartition permutation) B α Γ u a b goal union
  intro β j Δ whole l r keep pars held
  apply exact_OpenSourcePartitionAppend permutation whole l r (goal.relabel j) held
  intro γ k Ω joined through ap cmp
  let ρ := k ∘ j
  have chain := keepThrough j k keep through
  have pp := renameParser (u.relabel j) whole pars.source k Ω through
  have qq := renameParser u observed known ρ Ω chain
  have cb := moveCount observed certJoin cert ρ chain
  have l' := renameParser (a.relabel j) l pars.kept k Ω through
  have r' := renameParser (b.relabel j) r pars.removed k Ω through
  rw [formulaRelabelComposition j k goal]
  apply next γ ρ Ω (l.relabel k) (r.relabel k) joined chain
  · simpa only [ρ,← Term.relabel_relabel] using l'
  · simpa only [ρ,← Term.relabel_relabel] using r'
  · exact ap
  · apply sameSource (u.relabel ρ) (whole.relabel k) (observed.relabel ρ) joined (certJoin.relabel ρ)
    · simpa only [ρ,← Term.relabel_relabel] using pp
    · exact qq
    · exact cmp
    · exact cb

#print axioms exact_OriginalCertifiedSourceBalance
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedSourceBalanceProof
