module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJNilCarrierTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalJSingletonProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformCarrierProof
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof

/-! Proof of the frozen `ConditionalJNilCarrierTargets` (sha256 8ad148de…edb6). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJNilCarrierProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRulesSyntaxProof ID1Completion.InternalTermSubstitutionSyntaxProof
open ID1Completion.InternalGraphComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalJUnionTargets ConditionalJSingletonTargets ConditionalJNilCarrierTargets

/-- The J-carrier formula at numerals is the graph instance of the multiset-domain checker. -/
theorem multisetCarrierAsGraph (d : Data) (c x : Nat) :
    carrier (α := Empty) d true c (numeral x) =
      graph (OrdinaryArithmetic.graphFormula d.multiset) (numeral 1)
        (fun i => (numeral ((c ::ᵥ x ::ᵥ List.Vector.nil).get i) : OTerm Empty)) := by
  unfold carrier graph
  congr 1
  change ((OrdinaryArithmetic.graphFormula d.multiset).subst
      (Fin.cases (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![.var 0, .var 1])).subst
        ![numeral c, numeral x] =
    (OrdinaryArithmetic.graphFormula d.multiset).subst
      (Fin.cases (numeral 1) (fun i => numeral ((c ::ᵥ x ::ᵥ List.Vector.nil).get i)))
  rw [formulaSubstComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact numeralSubst 1 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      rfl

/-- The empty list code passes the original multiset-domain check. -/
theorem emptyTyped (S : Spine.Signature) (K : List Ty) :
    (checks S.entries (fixed S K)).multiset 0 = true := rfl

theorem exact_ActualNilCarrier : ActualNilCarrier := by
  intro S K i j r d evaluates c α Γ
  have one : evaluate (NumberedWindowInternalPresentationTargets.data i j r d).multiset
      (c ::ᵥ 0 ::ᵥ List.Vector.nil) = 1 := by
    change evaluate (NumberedWindowCheckerCoordinates.domain j) (c ::ᵥ 0 ::ᵥ List.Vector.nil) = 1
    rw [NumberedWindowCheckerCoordinatesProof.exact_ExactCoordinates.1, evaluates.2.1, emptyTyped]
    rfl
  obtain ⟨h⟩ := ID1Completion.InternalNumeralEvaluationStatementChecks.numeral_evaluation_exact
    (sourceBody (NumberedWindowInternalPresentationTargets.data i j r d) c) 2
    (NumberedWindowInternalPresentationTargets.data i j r d).multiset (c ::ᵥ 0 ::ᵥ List.Vector.nil) Empty
  rw [one, ← multisetCarrierAsGraph] at h
  -- move the closed derivation to the free-variable type α and the context Γ
  have hα := ID1Completion.InternalDerivationRenamingProof.actualDerivationRenaming _ Empty α
    Empty.elim [] _ ⟨h⟩
  obtain ⟨hα⟩ := hα
  rw [ConditionalJSingletonProof.carrierRelabelG] at hα
  have hz : (numeral 0 : OTerm Empty).relabel (Empty.elim : Empty → α) = OrdinaryArithmetic.zeroTerm :=
    ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel _
  rw [hz] at hα
  refine ⟨Derivation.weakening ?_ hα⟩
  intro p hp
  simp at hp

theorem exact_ActualJSingleton : ActualJSingleton := by
  intro S K i j r d evaluates c u sg hCU hMS hSC hNS hDG
  exact ConditionalJSingletonProof.exact_ConditionalJSingleton _ c u sg hCU hMS hSC
    (exact_ActualNilCarrier S K i j r d evaluates c) hNS hDG

theorem exact_ActualJMembers : ActualJMembers := by
  intro S K i j r d evaluates c u mem sg hCU hMS hSC hNS hDG hMG
  exact ConditionalJSingletonProof.exact_ConditionalJMembers _ c u mem sg hCU hMS hSC
    (exact_ActualNilCarrier S K i j r d evaluates c) hNS hDG hMG

#print axioms exact_ActualNilCarrier
#print axioms exact_ActualJSingleton
#print axioms exact_ActualJMembers

end LogicLineages.PersistentMarking.ConditionalJNilCarrierProof
