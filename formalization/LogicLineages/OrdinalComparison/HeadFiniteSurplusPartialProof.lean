module
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
open AdditiveHeadTree AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem free_head_partial {k Γ} (p : Policy)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (hf : ordinalHeadFree h = true) :
    ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
      AdmissiblePartial.run p 1 h = some v ∧ ∀ ν : OrdinalComponent Γ → Ordinal,
        denote ν (v (outputOne k)) = denote ν (ordinalHeadClosure h) + (surplus h : Ordinal) ∧
        denote ν (v (outputTwo k)) = (secondCount h : Ordinal) := by
  refine ⟨ordinalFreePartialVector 1 h, ?_, ?_⟩
  · rw [AdmissiblePartial.run.eq_def, if_pos hf]
  · intro ν
    rw [surplus_of_free h hf, secondCount_of_free h hf]
    simp only [Nat.cast_one]
    constructor
    · change ordinalNaturalSum (denote ν (ordinalHeadClosure h)) 1 =
        denote ν (ordinalHeadClosure h) + (1 : Ordinal)
      simpa using actualNaturalSumFiniteRight (denote ν (ordinalHeadClosure h)) 1
    · simp [ordinalFreePartialVector, outputTwo, denote]

theorem exactHeadPartial : Targets.ExactHeadPartial := by
  intro k Γ p h ht
  induction ht with
  | @free h hg hn => exact free_head_partial p h (headFree_of_inactive h hn)
  | tracked =>
    refine ⟨fun _ => .one, ?_, ?_⟩
    · rw [AdmissiblePartial.run.eq_def]
      simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs, UnaryCarrier.headIndex]
    · intro ν
      simp [denote, ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
        surplus, secondCount, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
  | @add a b ha hb iha ihb =>
    by_cases hf : ordinalHeadFree (.add a b) = true
    · exact free_head_partial p _ hf
    · obtain ⟨va,hva,hea⟩ := iha
      obtain ⟨vb,hvb,heb⟩ := ihb
      refine ⟨(fun j => AdmissiblePartial.three p .activeAdd (va j) (vb j) .one), ?_, ?_⟩
      · rw [AdmissiblePartial.run.eq_def, if_neg hf]
        simp [hva, hvb]
      · intro ν
        constructor
        · rw [three_value, (hea ν).1, (heb ν).1]
          simpa [denote, surplus, hf, ordinalHeadClosure, substitute] using
            finite_surplus_add (denote ν (ordinalHeadClosure a))
              (denote ν (ordinalHeadClosure b)) (surplus a) (surplus b)
        · rw [three_value, (hea ν).2, (heb ν).2]
          simpa [denote, secondCount, hf] using
            finite_count_add (secondCount a) (secondCount b)

end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Proof
