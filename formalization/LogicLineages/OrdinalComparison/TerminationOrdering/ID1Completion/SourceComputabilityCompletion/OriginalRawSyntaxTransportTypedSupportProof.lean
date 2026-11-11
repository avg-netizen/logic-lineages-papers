module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedAuxiliaryShift NumberedAuxiliarySubstitution
open OriginalRawSyntaxTransport
open NumberedAuxiliarySubstitutionSupportProof
open Source.SourceTypedPorts (variableIndex)

 def IndexErasure {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (sigma : Ty) (cutoff : Nat) : Prop :=
  ∀ {tau} (v : Variable Gamma tau), termCode (rho v) = eraseCode sigma cutoff (.var (variableIndex v))

 theorem shiftErasedVariable {Symbol : Type} (sigma : Ty) (cutoff index : Nat) :
    shiftCode 0 (eraseCode sigma cutoff (Code.var index : Code Symbol)) =
      eraseCode sigma (cutoff + 1) (Code.var (index + 1)) := by
  by_cases hb : index < cutoff
  · have hb' : index + 1 < cutoff + 1 := by omega
    simp [eraseCode, hb, hb', shiftCode, shiftVariable]
  · by_cases he : index = cutoff
    · subst index
      simp [eraseCode, shiftCode]
    · have hb' : ¬ index + 1 < cutoff + 1 := by omega
      have he' : index + 1 ≠ cutoff + 1 := by omega
      have hi : index - 1 + 1 = index := by omega
      simp [eraseCode, hb, hb', he, he', shiftCode, shiftVariable, hi]

 theorem liftIndexErasure {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    {boundType : Ty} (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (sigma : Ty) (cutoff : Nat) (h : IndexErasure rho sigma cutoff) :
    IndexErasure (liftSubstitution (sigma := boundType) rho) sigma (cutoff + 1) := by
  intro tau v
  cases v with
  | here => simp [liftSubstitution, termCode, variableIndex, eraseCode]
  | there v =>
    change termCode (rename (rho v) (Renaming.weaken Delta boundType)) =
      eraseCode sigma (cutoff + 1) (.var (variableIndex v + 1))
    have hw : termCode (rename (rho v) (Renaming.weaken Delta boundType)) = shiftCode 0 (termCode (rho v)) := by
      simpa only [prefixWeakening, List.length_nil, List.nil_append] using
        NumberedAuxiliaryShiftSupportProof.typedShiftCalibration Symbol arity [] Delta boundType tau (rho v)
    rw [hw, h v, shiftErasedVariable]

 theorem prefixIndexErasure {Symbol : Type} {arity : Symbol → Nat}
    (binders Gamma : List Ty) (sigma : Ty) :
    IndexErasure (prefixErasure (Symbol := Symbol) (arity := arity) binders Gamma sigma) sigma binders.length := by
  induction binders with
  | nil =>
    intro tau v
    cases v <;> simp [prefixErasure, singleSubstitution, termCode, variableIndex, eraseCode]
  | cons boundType binders ih =>
    exact liftIndexErasure (prefixErasure binders Gamma sigma) sigma binders.length ih

/-- Calibration of the EXISTING finite-environment code substitution to the
new cutoff erasure, using its actual lookup/lift suppliers. This is a native
syntax equation only, not a symbolic internal graph assertion. -/
 theorem environmentErasure {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta : List Ty)
      (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (sigma : Ty) (cutoff : Nat),
      IndexErasure rho sigma cutoff →
      substituteCode (substitutionCodes Gamma rho) (termCode q) = eraseCode sigma cutoff (termCode q) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty)
      (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (sigma : Ty) (cutoff : Nat),
      IndexErasure rho sigma cutoff →
      substituteCode (substitutionCodes Gamma rho) (argumentsCode args) = eraseCode sigma cutoff (argumentsCode args))
  case var v =>
    intro Delta rho sigma cutoff h
    simp only [termCode, substituteCode, environmentLookup v Delta rho, Option.getD_some]
    exact h v
  case lam body ih =>
    intro Delta rho sigma cutoff h
    simp only [termCode, substituteCode, eraseCode]
    rw [← liftEnvironmentCodes]
    exact congrArg (Code.lam _) (ih _ (liftSubstitution rho) sigma (cutoff + 1)
      (liftIndexErasure rho sigma cutoff h))
  case app f a ihf iha =>
    intro Delta rho sigma cutoff h
    simp only [termCode, substituteCode, eraseCode, ihf Delta rho sigma cutoff h, iha Delta rho sigma cutoff h]
  case bottom => intro Delta rho sigma cutoff h; rfl
  case ordinary f base ih =>
    intro Delta rho sigma cutoff h
    simp only [termCode, substituteCode, eraseCode, ih Delta rho sigma cutoff h]
  case numbered label f tau base types extras ihb ihe =>
    intro Delta rho sigma cutoff h
    simp only [termCode, substituteCode, eraseCode, ihb Delta rho sigma cutoff h, ihe Delta rho sigma cutoff h]
  case nil => rfl
  case cons =>
    rename_i Gamma elementType types q rest ihq ihr Delta rho sigma cutoff h
    simp only [argumentsCode, substituteCode, eraseCode, ihq Delta rho sigma cutoff h, ihr Delta rho sigma cutoff h]

 theorem typedErasure {Symbol : Type} {arity : Symbol → Nat} (binders Gamma : List Ty)
    (sigma tau : Ty) (q : AuxTerm Symbol arity (binders ++ sigma :: Gamma) tau) :
    termCode (substitute q (prefixErasure binders Gamma sigma)) = eraseCode sigma binders.length (termCode q) := by
  rw [NumberedAuxiliarySubstitutionSupportProof.typedSubstitutionCalibration]
  exact environmentErasure q _ (prefixErasure binders Gamma sigma) sigma binders.length
    (prefixIndexErasure binders Gamma sigma)

 theorem typedVariableCount {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : codeVariableCount (termCode q) = NumberedVariableCount.variableCount q := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => codeVariableCount (argumentsCode args) =
      NumberedVariableCount.argumentVariableCount args) <;>
    simp_all [termCode, argumentsCode, codeVariableCount,
      NumberedVariableCount.variableCount, NumberedVariableCount.argumentVariableCount]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
