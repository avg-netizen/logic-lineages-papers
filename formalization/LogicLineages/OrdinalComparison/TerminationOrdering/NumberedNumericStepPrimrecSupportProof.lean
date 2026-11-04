module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedTypedFocus NumberedStepContexts NumberedStepCertificate NumberedNumericStep
open NumberedNumericRoot NumberedUniformPackedDecoding NumberedUniformSelector
open NumberedFocusCode NumberedNumericStepPrimrec

theorem outputComparison (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma tau) :
    decide (some (termCode q) = some (termCode r)) =
      decide (packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma) =
        packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma)) := by
  have he : termCode q = termCode r ↔
      packedNumber (⟨tau,q⟩ : Packed (Fin n) arity Gamma) =
        packedNumber (⟨tau,r⟩ : Packed (Fin n) arity Gamma) := by
    constructor
    · intro h
      have hr := NumberedAuxiliaryCodingProof.termCodeInjective (Fin n) arity Gamma tau h
      cases hr
      rfl
    · intro h
      have hr := NumberedLeastCodeRepresentativeProof.packedNumberInjective n arity Gamma h
      exact congrArg (fun p : Packed (Fin n) arity Gamma => termCode p.2) hr
  simp only [Option.some.injEq,he]

theorem stepCalibration : NumberedNumericStepPrimrecTargets.ActualStepCalibration := by
  intro n arity symbols S Gamma table tau q r certificate
  unfold stepCodeTest
  rw [NumberedFocusCodeProof.focusCalibration]
  cases hf : focus certificate.path q with
  | none => simp [stepTest,hf]
  | some f =>
    simp only [Option.map_some,Option.any_some]
    rw [NumberedUniformPackedDecodingProof.rawPackedCalibration]
    cases hd : decodePackedNumber n arity f.holeGamma certificate.replacement with
    | none => simp [stepTest,hf,hd]
    | some replacement =>
      rcases replacement with ⟨sigma,replacement⟩
      simp only [Option.map_some,Option.any_some,packedCode]
      by_cases ht : sigma = f.holeType
      · subst sigma
        simp only [if_pos rfl]
        rw [NumberedFocusCodeProof.replacementCalibration n arity certificate.path Gamma tau q f replacement hf]
        have hselector :
            selectorCodeTest n arity symbols S f.holeGamma table
              (f.holeType,termCode f.value) (f.holeType,termCode replacement) certificate.root =
              (decodeSelector n arity f.holeGamma certificate.root).any (fun selector =>
                selectorTest n arity symbols S f.holeGamma table
                  ⟨f.holeType,f.value⟩ ⟨f.holeType,replacement⟩ selector) := by
          simpa only [packedCode] using
            (NumberedUniformSelectorProof.selectorCalibration n arity symbols S f.holeGamma table
              (⟨f.holeType,f.value⟩ : Packed (Fin n) arity f.holeGamma)
              (⟨f.holeType,replacement⟩ : Packed (Fin n) arity f.holeGamma) certificate.root)
        rw [hselector]
        rw [outputComparison n arity Gamma tau]
        cases hs : decodeSelector n arity f.holeGamma certificate.root <;>
          simp [stepTest,hf,hd,hs]
      · cases hs : decodeSelector n arity f.holeGamma certificate.root <;>
          simp [ht,stepTest,hf,hd,hs]

theorem numericStepCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (source target certificate : Nat) :
    numericStepDispatch n arity symbols S Gamma table source target certificate =
      numericStepTest n arity symbols S Gamma table source target certificate := by
  unfold numericStepDispatch numericStepTest
  rw [NumberedUniformPackedDecodingProof.rawUniverseCalibration,
    NumberedUniformPackedDecodingProof.rawPackedCalibration]
  cases hs : decodeUniverse n arity symbols S Gamma source with
  | none => rfl
  | some sourceTerm =>
    cases ht : decodePackedNumber n arity Gamma target with
    | none => rfl
    | some targetTerm =>
      cases hc : decodeStepCertificate certificate with
      | none => rfl
      | some data =>
        rcases sourceTerm with ⟨tau,q⟩
        rcases targetTerm with ⟨sigma,r⟩
        by_cases htype : sigma = tau
        · subst sigma
          simpa only [Option.map_some,packedCode,if_pos rfl,ite_true,dite_true] using
            stepCalibration n arity symbols S Gamma table tau q r data
        · simp [packedCode,htype]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecSupportProof
