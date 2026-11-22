module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalQuotientComparisonProof (actualOriginalComparison compareView)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A head equality test that is not zero forces internal equality: the
original trichotomy leaves only the equal case, since each strict order
makes the same actual test return zero. -/
theorem equalityOfHit (x y : OTerm α)
    (hit : Nonempty (Derivation body Γ (missGraph x y).not)) :
    Nonempty (Derivation body Γ (eqn x y)) := by
  obtain ⟨no⟩ := hit
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Γ)
  have hl : Nonempty (Derivation body (ltF x y :: Γ) (eqn x y)) := by
    obtain ⟨hz⟩ := rejectForwardOrder (body := body) (Gamma := ltF x y :: Γ) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have miss : Derivation body (ltF x y :: Γ) (missGraph x y) := hz
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination (addHyp no (ltF x y)) miss)⟩
  have hr : Nonempty (Derivation body (ltF y x :: Γ) (eqn x y)) := by
    obtain ⟨hz⟩ := rejectBackwardOrder (body := body) (Gamma := ltF y x :: Γ) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have miss : Derivation body (ltF y x :: Γ) (missGraph x y) := hz
    exact ⟨Derivation.explosion
      (Derivation.implicationElimination (addHyp no (ltF y x)) miss)⟩
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  have he : Derivation body Γ ((eqn x y).imp (eqn x y)) :=
    Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)
  have hrest : Derivation body Γ ((eqn x y ⊔ ltF y x).imp (eqn x y)) :=
    Derivation.implicationIntroduction
      (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
        (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) hrest⟩

/-- Transport the original scan along an internal equality of its
candidate. Seen, context and type are the same terms on both sides. -/
theorem candidateTransport (E : Program 4) (seen ctx ty h k : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn h k)))
    (scanned : Nonempty (Derivation body Γ (scanGraph E seen ctx ty h))) :
    Nonempty (Derivation body Γ (scanGraph E seen ctx ty k)) := by
  apply graphInputTransport body α 4 Γ _ (suc z)
    (![seen,ctx,ty,h] : Fin 4 → OTerm α) (![seen,ctx,ty,k] : Fin 4 → OTerm α) _ scanned
  intro i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) c) b) a) i
  all_goals rw [onEquality]
  all_goals first
    | exact same
    | exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl _⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
