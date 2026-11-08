module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedTypedCarrier NumberedQuotientApplication
open InternalFixedWindowVertexDispatch InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local instance] Classical.propDecidable

theorem constantEvaluation (n k : Nat) (v : List.Vector Nat n) :
    evaluate (constant n k) v = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (evaluate (constant n k) v) = Nat.succ k
    rw [ih]

theorem functionTypedEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (functionTyped data) v =
      evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
        (List.Vector.ofFn ![v.get 4,arrowCode (v.get 1) (v.get 2)]) := by
  change evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
    (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![Program.projection 4,consOf (.projection 1) (.projection 2)] :
        Fin 2 → Program 5) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · rfl
  · exact consOfEvaluation (.projection 1) (.projection 2) v

theorem argumentTypedEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (argumentTyped data) v =
      evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
        (List.Vector.ofFn ![v.get 3,v.get 1]) := by
  change evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
    (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![Program.projection 3,.projection 1] : Fin 2 → Program 5) i) v) = _
  congr 1

/-- Exact natural-number evaluation of all three guards, on every input.
This external lemma does not supply an internal derivation. -/
theorem activationEvaluation (window : Nat) (data : Data) (v : List.Vector Nat 5) :
    evaluate (activation window data) v =
      if Active window data (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)
        then 1 else 0 := by
  rw [activation,conjunctionEvaluation,sameEvaluation,constantEvaluation,
    conjunctionEvaluation,functionTypedEvaluation,argumentTypedEvaluation]
  change (if (if v.get 0 = window then 1 else 0) = 1 ∧
      (if evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
          (List.Vector.ofFn ![v.get 4,arrowCode (v.get 1) (v.get 2)]) = 1 ∧
        evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
          (List.Vector.ofFn ![v.get 3,v.get 1]) = 1 then 1 else 0) = 1
      then 1 else 0) = _
  by_cases hc : v.get 0 = window <;>
    by_cases hf : evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
      (List.Vector.ofFn ![v.get 4,arrowCode (v.get 1) (v.get 2)]) = 1 <;>
    by_cases ha : evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
      (List.Vector.ofFn ![v.get 3,v.get 1]) = 1 <;>
    simp only [Active,hc,hf,ha,if_true,if_false,and_self,and_true,and_false,Nat.zero_ne_one]

theorem activeBranchEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (activeBranch data) v =
      evaluate (InternalRepresentativeFoldCalibration.combine data.oldEdge)
        (List.Vector.ofFn ![v.get 1,v.get 2,v.get 4,v.get 3]) := by
  change evaluate (InternalRepresentativeFoldCalibration.combine data.oldEdge)
    (List.Vector.ofFn fun i : Fin 4 =>
      evaluate ((![Program.projection 1,.projection 2,.projection 4,.projection 3] :
        Fin 4 → Program 5) i) v) = _
  congr 1

/-- Recover only the original typed universe witness and its representative
equation. This is external source decoding, not internal graph reflection. -/
theorem typedValueWitness (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (tau : Ty) (value : Nat)
    (h : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma
      (List.Vector.ofFn ![value,typeNumber tau]) = 1) :
    ∃ q : Packed (Fin n) arity Gamma,
      InUniverse symbols S q.2 ∧ q.1 = tau ∧ representativeCode symbols S q = value := by
  change ((decodeType (typeNumber tau)).any (fun typ =>
    typedCanonicalCarrierTest n arity symbols S Gamma typ value)).toNat = 1 at h
  rw [NumberedNumericDecodingSupportProof.typeRoundTrip] at h
  have ht : typedCanonicalCarrierTest n arity symbols S Gamma tau value = true := by
    simpa only [Option.any_some,OrdinaryArithmeticQuotientProof.boolNatOne] using h
  exact (NumberedTypedCarrierProof.typedCanonicalCarrier
    n arity symbols S hc Gamma tau value).mp ht

theorem actualOriginalFixedWindowActiveVertexEquality :
    InternalFixedWindowVertexDispatchTargets.ActualOriginalFixedWindowActiveVertexEquality := by
  intro n arity symbols S Gamma table data hc hdata context domain codomain argument value hactive
  rcases hactive with ⟨hcontext,hfunction,hargument⟩
  subst context
  obtain ⟨sigma,_,hs⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal domain
  obtain ⟨tau,_,ht⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal codomain
  rw [← hs,← ht] at hfunction ⊢
  rw [← hs] at hargument
  change evaluate (InternalCertifiedSourceGuardSelection.typedChecker data)
    (List.Vector.ofFn ![value,typeNumber (.arrow sigma tau)]) = 1 at hfunction
  have htyped := InternalCertifiedSourceGuardSelectionEvaluationProof.typedCalibration
    n arity symbols S Gamma table data hc hdata
  have hf := (htyped (List.Vector.ofFn ![value,typeNumber (.arrow sigma tau)])).symm.trans hfunction
  have ha := (htyped (List.Vector.ofFn ![argument,typeNumber sigma])).symm.trans hargument
  obtain ⟨⟨fty,f⟩,hfU,hfty,hfx⟩ :=
    typedValueWitness n arity symbols S Gamma hc (.arrow sigma tau) value hf
  change fty = .arrow sigma tau at hfty
  subst fty
  obtain ⟨⟨aty,a⟩,haU,haty,hay⟩ :=
    typedValueWitness n arity symbols S Gamma hc sigma argument ha
  change aty = sigma at haty
  subst aty
  rw [← hfx,← hay]
  rw [InternalRepresentativeFoldCalibrationSupportProof.typedApplicationCombine
    n arity symbols S hc Gamma table data.oldEdge hdata.2.2.1 sigma tau f a hfU haU]
  unfold ApplicationCertificateLiftPath.vertex
  rw [OrdinaryArithmeticApplicationSupportProof.concreteCalibration,
    NumberedNumericApplicationProof.canonicalApplicationCalibration
      n arity symbols S hc Gamma sigma tau f a hfU haU]
  rfl

theorem actualOriginalFixedWindowVertexCalibration :
    InternalFixedWindowVertexDispatchTargets.ActualOriginalFixedWindowVertexCalibration := by
  intro n arity symbols S Gamma table data oldVertex hc hdata hold v
  rw [vertex,evalBranch,activationEvaluation]
  by_cases ha : Active (OrdinaryArithmeticQuotient.contextCode symbols S table) data
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)
  · rw [if_pos ha]
    simp only [Nat.one_ne_zero,if_false]
    rw [activeBranchEvaluation]
    exact actualOriginalFixedWindowActiveVertexEquality
      n arity symbols S Gamma table data hc hdata
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) ha
  · rw [if_neg ha]
    exact hold v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchEvaluationProof
