module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorValuesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain
open SourceCollisionCompletion (rawScalar)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- A genuine ordinal finite-tail bound, not an assumed source evaluator. -/
theorem appValue_lower (h : Ordinal) (he : h<epsilonZero) (s q : Nat) :
    s+q≤appValue h s q :=
  actualCollapseFiniteTailBound (ordinalNaturalProduct Ordinal.omega0 h)
    (omega_product_below h he) (s+q)

theorem unaryApp_lower {Γ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    value0 ρ a+rawScalar (valuation ρ) q≤rawScalar (valuation ρ) (.app a q) := by
  rw [unaryApp]
  exact appValue_lower _ (values_facts ρ a).2.2.1 _ _

theorem zero_value {Γ} (ρ : AdmissibleSubstitution Γ) :
    rawScalar (valuation ρ) (.zeroC : OriginalTerm Γ .ground)=1 := by
  apply SourceCollisionCompletion.Proof.raw_of_assignment _ _ (fun _ => .one) 1 rfl
  simp only [denote,Nat.cast_one]

/-- Four actual nested applications, all sharing the SAME literal payload.
The initial source zero has raw canonical scalar one. -/
theorem payload_bound {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    1+value0 ρ (combine a a)+value0 ρ (combine b b)+
      value0 ρ (combine a b)+value0 ρ (combine b a)≤rawScalar (valuation ρ) (payload a b) := by
  have hX := unaryApp_lower ρ (combine a a) (.zeroC : OriginalTerm Γ .ground)
  have hY := unaryApp_lower ρ (combine b b) (.app (combine a a) .zeroC)
  have hZ := unaryApp_lower ρ (combine a b) (.app (combine b b) (.app (combine a a) .zeroC))
  have hW := unaryApp_lower ρ (combine b a)
    (.app (combine a b) (.app (combine b b) (.app (combine a a) .zeroC)))
  rw [zero_value] at hX
  unfold payload
  omega

theorem payload_five {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    5≤rawScalar (valuation ρ) (payload a b) := by
  have hb := payload_bound ρ a b
  have hx := (values_facts ρ (combine a a)).1
  have hy := (values_facts ρ (combine b b)).1
  have hz := (values_facts ρ (combine a b)).1
  have hw := (values_facts ρ (combine b a)).1
  omega

theorem payload_components {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    value0 ρ (combine a a)≤rawScalar (valuation ρ) (payload a b) ∧
    value0 ρ (combine b b)≤rawScalar (valuation ρ) (payload a b) ∧
    value0 ρ (combine a b)≤rawScalar (valuation ρ) (payload a b) ∧
    value0 ρ (combine b a)≤rawScalar (valuation ρ) (payload a b) := by
  have hb := payload_bound ρ a b
  omega
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
