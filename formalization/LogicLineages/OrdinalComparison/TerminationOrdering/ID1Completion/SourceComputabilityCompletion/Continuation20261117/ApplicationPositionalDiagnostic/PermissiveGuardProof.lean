module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderMachineCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.PermissiveGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem allowValue : OriginalUniverseDecoder.programValue2 allow = fun _ _ => 1 := by
  funext x y
  exact OriginalRawSyntaxTransportEvaluationSupportProof.constantEvaluation 2 1 _

theorem transition (H : Nat → Nat) (state context : Nat) :
    OriginalUniverseDecoder.transitionValue H (fun _ _ => 1) (fun _ _ => 1) state context =
      OriginalTypedDecoder.transitionValue H state := by
  by_cases hs : (Nat.unpair state).1 = 1
  · by_cases hw : (Nat.unpair state).2 = 0
    · simp [OriginalUniverseDecoder.transitionValue, OriginalTypedDecoder.transitionValue, hs, hw]
    · by_cases h0 : OriginalTypedDecoder.requestMode (Nat.unpair ((Nat.unpair state).2 - 1)).1 = 0
      · simp [OriginalUniverseDecoder.transitionValue, OriginalUniverseDecoder.guardValue, hs, hw, h0]
      · by_cases h1 : OriginalTypedDecoder.requestMode (Nat.unpair ((Nat.unpair state).2 - 1)).1 = 1
        · simp [OriginalUniverseDecoder.transitionValue, OriginalUniverseDecoder.guardValue, hs, hw, h0, h1]
        · simp [OriginalUniverseDecoder.transitionValue, OriginalUniverseDecoder.guardValue,
            OriginalTypedDecoder.transitionValue, OriginalTypedDecoder.expandValue, hs, hw, h0, h1]
  · simp [OriginalUniverseDecoder.transitionValue, OriginalTypedDecoder.transitionValue, hs]

theorem iterate (H : Nat → Nat) (count initial context : Nat) :
    OriginalUniverseDecoder.iterateValue H (fun _ _ => 1) (fun _ _ => 1) count initial context =
      OriginalTypedDecoder.iterateValue H count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change OriginalUniverseDecoder.transitionValue H (fun _ _ => 1) (fun _ _ => 1)
      (OriginalUniverseDecoder.iterateValue H (fun _ _ => 1) (fun _ _ => 1) count initial context) context =
      OriginalTypedDecoder.transitionValue H (OriginalTypedDecoder.iterateValue H count initial)
    rw [ih, transition]

theorem checkerEqualsTyped (H : Program 1) (typ raw gamma context : Nat) :
    evaluate (OriginalUniverseDecoder.termCheck H allow allow)
      (List.Vector.ofFn ![typ,raw,gamma,context]) =
    evaluate (OriginalTypedDecoder.termCheck H) (List.Vector.ofFn ![typ,raw,gamma]) := by
  rw [OriginalUniverseDecoderMachineCalibrationProof.termCheckEvaluation,
    OriginalTypedDecoderMachineCalibrationProof.termCheckEvaluation]
  simp only [List.Vector.get_ofFn, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, allowValue,
    OriginalUniverseDecoder.checkValue, OriginalTypedDecoder.checkValue, iterate]
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.PermissiveGuardProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.PermissiveGuardProof
