module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionSupportProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedAuxiliaryShift NumberedAuxiliarySubstitution
open Source.SourceTypedPorts (variableIndex)

theorem environmentLookup {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (v : Variable Gamma tau) : ∀ (Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    (substitutionCodes Gamma rho)[variableIndex v]?=some (termCode (rho v)) := by
  induction v with
  | here => intro Delta rho; rfl
  | there v ih =>
    intro Delta rho
    exact ih Delta (fun v => rho (.there v))

theorem weakeningEnvironment {Symbol : Type} {arity : Symbol → Nat} :
    ∀ (Gamma Delta : List Ty) (sigma : Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    substitutionCodes Gamma (fun v => rename (rho v) (Renaming.weaken Delta sigma))=
      (substitutionCodes Gamma rho).map (shiftCode 0) := by
  intro Gamma
  induction Gamma with
  | nil => intro Delta sigma rho; rfl
  | cons tau Gamma ih =>
    intro Delta sigma rho
    simp only [substitutionCodes,List.map_cons]
    have hc : termCode (rename (rho .here) (Renaming.weaken Delta sigma))=shiftCode 0 (termCode (rho .here)) := by
      simpa only [prefixWeakening,List.length_nil,List.nil_append] using
        (NumberedAuxiliaryShiftSupportProof.typedShiftCalibration Symbol arity [] Delta sigma tau (rho .here))
    rw [hc]
    rw [ih Delta sigma (fun v => rho (.there v))]

theorem liftEnvironmentCodes {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (sigma : Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) :
    substitutionCodes (sigma::Gamma) (liftSubstitution rho)=liftEnvironment (substitutionCodes Gamma rho) := by
  change Code.var 0 :: substitutionCodes Gamma (fun v => rename (rho v) (Renaming.weaken Delta sigma))=
    Code.var 0 :: (substitutionCodes Gamma rho).map (shiftCode 0)
  exact congrArg (List.cons (Code.var 0)) (weakeningEnvironment Gamma Delta sigma rho)

theorem substituteCodeCalibration {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      termCode (substitute q rho)=substituteCode (substitutionCodes Gamma rho) (termCode q) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty)
      (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
        argumentsCode (substituteArguments args rho)=substituteCode (substitutionCodes Gamma rho) (argumentsCode args))
  case var v =>
    intro Delta rho
    simp only [substitute,termCode,substituteCode,environmentLookup v Delta rho,Option.getD_some]
  case lam body ih =>
    intro Delta rho
    simp only [substitute,termCode,substituteCode]
    rw [ih _ (liftSubstitution rho),liftEnvironmentCodes]
  case app f a ihf iha =>
    intro Delta rho
    simp only [substitute,termCode,substituteCode,ihf Delta rho,iha Delta rho]
  case bottom => intro Delta rho; rfl
  case ordinary f base ih =>
    intro Delta rho
    simp only [substitute,termCode,substituteCode,ih Delta rho]
  case numbered k f tau base types extras ihb ihe =>
    intro Delta rho
    simp only [substitute,termCode,substituteCode,ihb Delta rho,ihe Delta rho]
  case nil => rfl
  case cons =>
    rename_i Gamma sigma types q rest ihq ihr Delta rho
    simp only [substituteArguments,argumentsCode,substituteCode,ihq Delta rho,ihr Delta rho]

theorem typedSubstitutionCalibration : NumberedAuxiliarySubstitutionTargets.ActualTypedSubstitutionCalibration := by
  intro Symbol arity Gamma Delta tau q rho
  exact substituteCodeCalibration q Delta rho

theorem argumentSubstitutionCalibration : NumberedAuxiliarySubstitutionTargets.ActualArgumentSubstitutionCalibration := by
  intro Symbol arity Gamma Delta types args rho
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest =>
      simp only [substituteArguments,argumentsCode,substituteCode,substituteCodeCalibration q Delta rho,ih rest]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionSupportProof
