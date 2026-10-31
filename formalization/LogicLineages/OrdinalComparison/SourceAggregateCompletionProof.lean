module
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionTargets
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAggregateCompletion.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open SourceCollisionCompletion SourceCollisionCompletion.Proof OriginalDomain

theorem raw_zero {Γ} (ν : OrdinalComponent Γ → Ordinal) :
    rawScalar ν (.zeroC : OriginalTerm Γ .ground) = 1 := by
  apply raw_of_assignment ν .zeroC (fun _ => .one) 1 rfl
  simp [denote]

theorem all_equal_cons {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    AllEqual ν ((p,q)::es) ↔ rawScalar ν p = rawScalar ν q ∧ AllEqual ν es := by
  constructor
  · intro h
    exact ⟨h (p,q) (by simp), fun e he => h e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨h, ht⟩ e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact h
    · exact ht e he

theorem combine_numeric (a b c d : Nat) (hab : b ≤ a) (hcd : d ≤ c) :
    g (3*b+d+2) ≤ g (3*a+c+2) ∧
    (g (3*a+c+2) = g (3*b+d+2) ↔ a = b ∧ c = d) ∧
    (¬ (a = b ∧ c = d) → 2 ≤ g (3*a+c+2) - g (3*b+d+2)) := by
  refine ⟨g_strictMono.monotone (by omega), ?_, ?_⟩
  · constructor
    · intro h
      have := g_strictMono.injective h
      omega
    · rintro ⟨rfl, rfl⟩
      rfl
  · intro h
    have hn : 3*b+d+2 < 3*a+c+2 := by omega
    have hg := g_four_lt _ _ hn
    have hp := g_positive (3*b+d+2)
    omega

theorem admissible_aggregate (Γ : List Ty)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground))
    (ρ : AdmissibleSubstitution Γ) : AggregateAt (valuation ρ) es := by
  induction es with
  | nil =>
    simp [AggregateAt, aggregate, AllEqual, raw_zero]
  | cons e es ih =>
    rcases e with ⟨p,q⟩
    have hd := admissible_collision Γ p q ρ
    unfold CollisionAt at hd
    unfold AggregateAt at ih ⊢
    have hc := combine_numeric
      (rawScalar (valuation ρ) (detectorLeft p q))
      (rawScalar (valuation ρ) (detectorRight p q))
      (rawScalar (valuation ρ) (aggregate es).1)
      (rawScalar (valuation ρ) (aggregate es).2) hd.1 ih.1
    have he :
        (rawScalar (valuation ρ) (detectorLeft p q) = rawScalar (valuation ρ) (detectorRight p q) ∧
          rawScalar (valuation ρ) (aggregate es).1 = rawScalar (valuation ρ) (aggregate es).2) ↔
          AllEqual (valuation ρ) ((p,q)::es) := by
      rw [hd.2.1, ih.2.1, all_equal_cons]
    simp only [aggregate]
    rw [actualGroundEraser Γ (detectorLeft p q) (aggregate es).1 ρ,
      actualGroundEraser Γ (detectorRight p q) (aggregate es).2 ρ]
    exact ⟨hc.1, hc.2.1.trans he, fun h => hc.2.2 (fun h' => h (he.mp h'))⟩

theorem fullSourceAggregate : Targets.FullSourceAggregate := by
  refine ⟨admissible_aggregate, ?_⟩
  intro Γ es S ρ
  obtain ⟨ρ', he⟩ := originalSupportedExtension Γ S ρ
  have hv : valuation ρ' = supportedValuation ρ := funext he
  rw [← hv]
  exact admissible_aggregate Γ es ρ'
end LogicLineages.OrdinalComparison.Source.SourceAggregateCompletion.Proof
