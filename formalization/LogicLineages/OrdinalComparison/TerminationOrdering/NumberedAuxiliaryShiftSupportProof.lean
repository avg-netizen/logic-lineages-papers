module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftSupportProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedAuxiliaryShift
open Source.SourceTypedPorts (variableIndex)

def IndexShift {Gamma Delta : List Ty} (rho : Renaming Gamma Delta) (cutoff : Nat) : Prop :=
  ∀ {tau} (v : Variable Gamma tau),variableIndex (rho v)=shiftVariable cutoff (variableIndex v)

theorem shiftSuccessor (cutoff index : Nat) :
    shiftVariable (cutoff+1) (index+1)=shiftVariable cutoff index+1 := by
  unfold shiftVariable
  split <;> split <;> omega

theorem liftIndexShift {Gamma Delta : List Ty} {sigma : Ty} (rho : Renaming Gamma Delta)
    (cutoff : Nat) (h : IndexShift rho cutoff) : IndexShift (Renaming.lift (τ := sigma) rho) (cutoff+1) := by
  intro tau v
  cases v with
  | here => simp [Renaming.lift,variableIndex,shiftVariable]
  | there v =>
    change variableIndex (rho v)+1=shiftVariable (cutoff+1) (variableIndex v+1)
    rw [h v,shiftSuccessor]

theorem prefixIndexShift (binders Gamma : List Ty) (sigma : Ty) :
    IndexShift (prefixWeakening binders Gamma sigma) binders.length := by
  induction binders with
  | nil => intro tau v; simp [prefixWeakening,Renaming.weaken,variableIndex,shiftVariable]
  | cons tau binders ih =>
    exact liftIndexShift (prefixWeakening binders Gamma sigma) binders.length ih

theorem renameCodeCalibration {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta : List Ty) (rho : Renaming Gamma Delta)
      (cutoff : Nat),IndexShift rho cutoff → termCode (rename q rho)=shiftCode cutoff (termCode q) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta)
      (cutoff : Nat),IndexShift rho cutoff →
        argumentsCode (renameArguments args rho)=shiftCode cutoff (argumentsCode args))
  case var v =>
    intro Delta rho cutoff h
    exact congrArg Code.var (h v)
  case lam body ih =>
    intro Delta rho cutoff h
    simp only [rename,termCode,shiftCode]
    exact congrArg (Code.lam _) (ih _ (Renaming.lift rho) (cutoff+1) (liftIndexShift rho cutoff h))
  case app f a ihf iha =>
    intro Delta rho cutoff h
    simp only [rename,termCode,shiftCode,ihf Delta rho cutoff h,iha Delta rho cutoff h]
  case bottom => intro Delta rho cutoff h; rfl
  case ordinary f base ih =>
    intro Delta rho cutoff h
    simp only [rename,termCode,shiftCode,ih Delta rho cutoff h]
  case numbered k f tau base types extras ihb ihe =>
    intro Delta rho cutoff h
    simp only [rename,termCode,shiftCode,ihb Delta rho cutoff h,ihe Delta rho cutoff h]
  case nil => rfl
  case cons =>
    rename_i Gamma sigma types q rest ihq ihr Delta rho cutoff h
    simp only [renameArguments,argumentsCode,shiftCode,ihq Delta rho cutoff h,ihr Delta rho cutoff h]

theorem typedShiftCalibration : NumberedAuxiliaryShiftTargets.ActualTypedShiftCalibration := by
  intro Symbol arity binders Gamma sigma tau q
  exact renameCodeCalibration q _ (prefixWeakening binders Gamma sigma) binders.length
    (prefixIndexShift binders Gamma sigma)

theorem argumentsCodeCalibration {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) (Delta : List Ty) (rho : Renaming Gamma Delta)
    (cutoff : Nat) (h : IndexShift rho cutoff) :
    argumentsCode (renameArguments args rho)=shiftCode cutoff (argumentsCode args) := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest =>
      simp only [renameArguments,argumentsCode,shiftCode,renameCodeCalibration q Delta rho cutoff h,ih rest]

theorem argumentShiftCalibration : NumberedAuxiliaryShiftTargets.ActualArgumentShiftCalibration := by
  intro Symbol arity binders Gamma types sigma args
  exact argumentsCodeCalibration args _ (prefixWeakening binders Gamma sigma) binders.length
    (prefixIndexShift binders Gamma sigma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryShiftSupportProof
