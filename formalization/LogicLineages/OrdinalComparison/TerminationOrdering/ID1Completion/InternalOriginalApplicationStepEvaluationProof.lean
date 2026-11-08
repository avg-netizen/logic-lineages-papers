module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepEvaluationProof
open Source InternalOriginalApplicationStep

/-- Compose all-input calibration only for the literal selected ASTs.
None of these external equations is used as an internal derivation rule. -/
theorem selectedCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data)
    (h : Calibrated n arity symbols S Gamma table data) :
    SelectedCalibrated n arity symbols S Gamma table data := by
  have hv := InternalApplicationValidityCalibrationProof.actualOriginalRecursiveValidityCalibration
    n arity symbols S Gamma data.oldValidity data.member h.1 h.2.1
  have he := InternalStructuralEndpointGuardProof.actualOriginalStructuralEndpointCalibration
    n arity symbols S Gamma (validity data) data.member hv h.2.1
  have hc := InternalApplicationStepCheckerProof.actualOriginalCheckerCalibration
    n arity symbols S Gamma table (endpoint data) data.oldStep he h.2.2
  have hs := InternalOriginalStepGuardProof.actualOriginalGuardedStepCalibration
    n arity symbols S Gamma table (validity data) (normalizedCore data) hv hc
  exact ⟨hv,he,hs⟩

/-- The same finite leaves precede all internal inputs. The old step is the
already calibrated original numeric step program; representatives are unused. -/
theorem calibratedDataExists (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    ∃ data : Data, Calibrated n arity symbols S Gamma table data := by
  obtain ⟨oldValidity,hv⟩ := InternalOriginalStepGuardProof.actualOriginalValidityProgramsExist
    n arity symbols S Gamma
  obtain ⟨member,hm⟩ := InternalStructuralEndpointGuardProof.actualOriginalMembershipProgramExists S
  obtain ⟨oldEdge,he⟩ := InternalQuotientEdgeCheckerEvaluationProof.actualOriginalProgramsExist
    n arity symbols S Gamma table
  exact ⟨⟨oldValidity,member,oldEdge.stepProgram⟩,hv,hm,he.1⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepEvaluationProof
