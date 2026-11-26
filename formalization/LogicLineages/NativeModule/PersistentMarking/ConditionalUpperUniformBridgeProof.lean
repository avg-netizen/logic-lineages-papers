module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTagProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformInstanceProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformCarrierProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalPresentationChecks
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof

/-! The bridge `UniformToIndividual`: at programs evaluating the window's original checks, the
uniform all-terms sentence gives the individual I-atom `I(numeral (2x))` of every admitted scalar
address x, via steps (i)–(iii) and one internal equality elimination. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformBridgeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalTermSubstitutionProof
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding varBind)
open NumberedWindowExternalIDOperators NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowPresentationClauses
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalUpperUniformTargets

/-- The predicate atom as an instance of its open form. -/
theorem predicateInstance (y : OTerm Empty) :
    instantiate (Positive.predicate (.var (.inr (0 : Fin 1)) : OTerm (Empty ⊕ Fin 1))).formula (emb y) =
      (Positive.predicate y).formula := by
  unfold instantiate
  rw [bindEmbedding, ← predicateSubstitution, varBind]

/-- An admitted address passes the original scalar check of the presentation. -/
theorem scalarOfAdmitted (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K) (x : Nat)
    (hx : NumberedWindowArithmeticAllContextTargets.AdmittedAddress S K x) :
    (checks S.entries (fixed S K)).scalar x = true := by
  let P : Nat → Prop := fun z => ∃ y, (checks S.entries (fixed S K)).scalar y = true ∧ z = 2 * y
  have all := ((NumberedWindowOriginalPresentationChecks.exact_ActualOperatorAndTerms S K hk P).2).mp
    (fun y hy => ⟨y, hy, rfl⟩)
  obtain ⟨y, hy, heq⟩ := all x hx
  have : x = y := by
    change 2 * x = 2 * y at heq
    omega
  rw [this]
  exact hy

theorem exact_UniformToIndividual : UniformToIndividual := by
  intro S K hk i j r d c evaluates uniform x hx
  let B := sourceBody (NumberedWindowInternalPresentationTargets.data i j r d) c
  have one : evaluate (NumberedWindowInternalPresentationTargets.data i j r d).scalar
      (c ::ᵥ x ::ᵥ List.Vector.nil) = 1 := by
    change evaluate (NumberedWindowCheckerCoordinates.domain i) (c ::ᵥ x ::ᵥ List.Vector.nil) = 1
    rw [NumberedWindowCheckerCoordinatesProof.exact_ExactCoordinates.1, evaluates.1, scalarOfAdmitted S K hk x hx]
    rfl
  obtain ⟨implication⟩ := ConditionalUpperUniformInstanceProof.exact_AllTermsInstance B _ c x uniform
  obtain ⟨carrierProof⟩ := ConditionalUpperUniformCarrierProof.exact_ScalarCarrierNumeralTruth B _ c x one
  have member := Derivation.implicationElimination implication carrierProof
  obtain ⟨tagEq⟩ := ConditionalUpperUniformTagProof.exact_EvenTagNumeral B Empty x
  rw [ID1Completion.InternalSourceInversionSupportProof.onEquality] at tagEq
  have start : Derivation B []
      (instantiate (Positive.predicate (.var (.inr (0 : Fin 1)) : OTerm (Empty ⊕ Fin 1))).formula
        (emb (tagTerm false (numeral x)))) := by
    rw [predicateInstance]
    exact member
  have finish := Derivation.equalityElimination _ _ _ tagEq start
  rw [predicateInstance] at finish
  exact ⟨finish⟩

#print axioms exact_UniformToIndividual

end LogicLineages.PersistentMarking.ConditionalUpperUniformBridgeProof
