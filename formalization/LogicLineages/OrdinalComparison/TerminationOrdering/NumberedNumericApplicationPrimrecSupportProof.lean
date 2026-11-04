module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecSupportProof
open Source NumberedNumericCarrier NumberedNumericApplication NumberedNumericApplicationPrimrec
open NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedQuotientApplication

theorem calibration : NumberedNumericApplicationPrimrecTargets.ActualApplicationProgramCalibration := by
  intro n arity symbols S Gamma sigma tau x y
  cases hf : decodeUniverse n arity symbols S Gamma x with
  | none => simp [applicationProgram,canonicalApplication,hf]
  | some f =>
    cases ha : decodeUniverse n arity symbols S Gamma y with
    | none => simp [applicationProgram,canonicalApplication,hf,ha]
    | some a =>
      rcases f with ⟨fty,f⟩
      rcases a with ⟨aty,a⟩
      by_cases ht : fty = .arrow sigma tau
      · subst fty
        by_cases hu : aty=sigma
        · subst aty
          have hround : decodePacked arity Gamma (tau,Code.app sigma (termCode f) (termCode a)) = some (applicationPacked f a) :=
            NumberedAuxiliaryDecodingProof.packedRoundTrip (Fin n) arity Gamma (applicationPacked f a)
          simp [applicationProgram,canonicalApplication,hf,ha,hround]
        · simp [applicationProgram,canonicalApplication,hf,ha,hu]
      · simp [applicationProgram,canonicalApplication,hf,ha,ht]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecSupportProof
