module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardEvaluationProof
open Source NumberedRewriteReduction NumberedNumericDecoding NumberedLeastCodeRepresentative
open NumberedNumericQuotientEdge NumberedTypedCarrier InternalQuotientEdgeTypeGuard
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original step soundness and subtype preservation supply target membership.
The original typed canonical theorem is then applied to BOTH representatives. -/
theorem actualOriginalQuotientEdgeTypedEndpoints :
    InternalQuotientEdgeTypeGuardTargets.ActualOriginalQuotientEdgeTypedEndpoints := by
  intro n arity symbols S Gamma table hS x y certificate hedge
  obtain ⟨tau,q,r,hq,hstep,hx,hy⟩ :=
    (NumberedNumericQuotientEdgeProof.numericQuotientEdge
      n arity symbols S Gamma table x y).mp ⟨certificate,hedge⟩
  have hr := NumberedWindowReductionProof.stepGood symbols S hS hstep hq
  have hxt : typedCanonicalCarrierTest n arity symbols S Gamma tau x = true :=
    (NumberedTypedCarrierProof.typedCanonicalCarrier n arity symbols S hS Gamma tau x).mpr
      ⟨⟨tau,q⟩,hq,rfl,hx⟩
  have hyt : typedCanonicalCarrierTest n arity symbols S Gamma tau y = true :=
    (NumberedTypedCarrierProof.typedCanonicalCarrier n arity symbols S hS Gamma tau y).mpr
      ⟨⟨tau,r⟩,hr,rfl,hy⟩
  have htag : (Nat.unpair x).1 = typeNumber tau := by
    rw [← hx]
    exact InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeOuterType
      n arity symbols S Gamma (⟨tau,q⟩ : Packed (Fin n) arity Gamma)
  constructor
  · change ((decodeType (Nat.unpair x).1).any
      (fun tau => typedCanonicalCarrierTest n arity symbols S Gamma tau x)).toNat = 1
    rw [htag,NumberedNumericDecodingProof.typeNumericRoundTrip]
    simp only [Option.any_some,hxt,Bool.toNat_true]
  · change ((decodeType (Nat.unpair x).1).any
      (fun tau => typedCanonicalCarrierTest n arity symbols S Gamma tau y)).toNat = 1
    rw [htag,NumberedNumericDecodingProof.typeNumericRoundTrip]
    simp only [Option.any_some,hyt,Bool.toNat_true]

theorem sourceTypeEvaluation (v : List.Vector Nat 3) :
    evaluate sourceType v = (Nat.unpair (v.get 0)).1 := by
  unfold sourceType
  rw [leftOfEvaluation]
  rfl

theorem typedAtEvaluation (typedProgram : Program 2) (endpoint : Fin 3)
    (v : List.Vector Nat 3) :
    evaluate (typedAt typedProgram endpoint) v =
      evaluate typedProgram (List.Vector.ofFn ![v.get endpoint,(Nat.unpair (v.get 0)).1]) := by
  change evaluate typedProgram (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((![.projection endpoint,sourceType] : Fin 2 → Program 3) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases (sourceTypeEvaluation v) (fun j => Fin.elim0 j)) i

/-- Rejected original inputs remain zero independently of the new guards.
Accepted original inputs satisfy both guards by the preceding semantic result. -/
theorem actualOriginalQuotientEdgeTypedWrapperCalibration :
    InternalQuotientEdgeTypeGuardTargets.ActualOriginalQuotientEdgeTypedWrapperCalibration := by
  intro n arity symbols S Gamma table data typedProgram hS hdata htyped v
  have hcore := InternalQuotientEdgeCheckerEvaluationProof.actualOriginalCheckerCalibration
    n arity symbols S Gamma table data hdata v
  rw [checker,actualConjunctionEvaluation,actualConjunctionEvaluation,
    typedAtEvaluation,typedAtEvaluation,htyped,htyped,hcore]
  cases hedge : numericEdgeTest n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) with
  | false => simp only [Bool.toNat_false,Nat.zero_ne_one,false_and,ite_false]
  | true =>
    obtain ⟨hx,hy⟩ := actualOriginalQuotientEdgeTypedEndpoints
      n arity symbols S Gamma table hS (v.get 0) (v.get 1) (v.get 2) hedge
    rw [hx,hy]
    rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardEvaluationProof
