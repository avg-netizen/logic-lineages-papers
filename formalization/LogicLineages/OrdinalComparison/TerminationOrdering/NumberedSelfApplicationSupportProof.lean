module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationSupportProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedAuxiliaryCoding
open NumberedRewriteSyntax NumberedRewriteReduction NumberedSelectCertificate NumberedSelfApplication

theorem typedSelfArgumentsCalibration : NumberedSelfApplicationTargets.ActualTypedSelfArgumentsCalibration := by
  intro Symbol arity Gamma k f base extraTypes extras types
  induction types with
  | nil => exact ⟨rfl,rfl⟩
  | cons tau types ih =>
    constructor <;> simp only [selfArguments,argumentsCode,termCode,selfCode,argumentList,packedCode,
      List.map_cons,selfEntries,ih.1,ih.2]

theorem typedApplicationCalibration : NumberedSelfApplicationTargets.ActualTypedApplicationCalibration := by
  intro Symbol arity Gamma types
  induction types with
  | nil => intro tau q args; cases args; rfl
  | cons sigma types ih =>
    intro tau q args
    cases args with
    | cons a rest => exact ih tau (AuxTerm.app q a) rest

theorem selectCodeCalibration : NumberedSelfApplicationTargets.ActualSelectCodeCalibration := by
  intro n arity Gamma types index q
  rcases q with ⟨tau,q⟩
  cases q with
  | var v => rfl
  | lam body => rfl
  | app f a => rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | numbered k f tau base extraTypes extras =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [termCode,selectCode,selectTarget,NumberedExchangeCalibrationSupportProof.argumentEntriesCalibration,
        Option.bind_eq_bind,Option.bind_some]
      rw [←List.map_append,List.getElem?_map]
      cases hs : (argumentList base++argumentList extras)[index]? with
      | none => simp only [hs,Option.map_none,Option.bind_none]
      | some selected =>
        rcases selected with ⟨sigma,selected⟩
        simp only [hs,Option.map_some,Option.bind_some,packedCode]
        by_cases ht : sigma=arrows types tau
        · simp only [if_pos ht,dif_pos ht,Option.map_some,Option.pure_def]
          rw [typedApplicationCalibration,
            (typedSelfArgumentsCalibration (Fin n) arity Gamma k f base extraTypes extras types).2,
            NumberedExchangeCalibrationSupportProof.termCodeCast]
        · simp only [if_neg ht,dif_neg ht,Option.map_none]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationSupportProof
