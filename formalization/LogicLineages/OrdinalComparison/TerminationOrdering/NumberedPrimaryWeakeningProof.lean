module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryWeakening

theorem liftVariables {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (rho : Renaming Gamma Delta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma :: Gamma) tau) => AuxTerm.var (arity := arity) (rho.lift v)) =
    (fun {tau} (v : Variable (sigma :: Gamma) tau) => liftSubstitution (fun v => AuxTerm.var (arity := arity) (rho v)) v) := by
  funext tau v
  cases v <;> rfl

theorem renameAsSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
    NumberedRewriteSyntax.rename q rho = substitute q (fun v => AuxTerm.var (rho v)) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
      renameArguments args rho = substituteArguments args (fun v => AuxTerm.var (rho v)))
  case var v => intros; rfl
  case lam body ih =>
    intro Delta rho
    simp only [NumberedRewriteSyntax.rename,substitute]
    rw [ih _ rho.lift,liftVariables]
  case app f a ihf iha =>
    intro Delta rho
    exact congrArg₂ AuxTerm.app (ihf Delta rho) (iha Delta rho)
  case bottom => intros; rfl
  case ordinary f base ih =>
    intro Delta rho
    exact congrArg (AuxTerm.ordinary f) (ih Delta rho)
  case numbered k f tau base types extras ihb ihe =>
    intro Delta rho
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e) (ihb Delta rho) (ihe Delta rho)
  case nil => intros; rfl
  case cons Gamma sigma types q rest ihq ihr Delta rho =>
    exact congrArg₂ AuxArguments.cons (ihq Delta rho) (ihr Delta rho)

theorem actualTermRenameAsSubstitution : NumberedPrimaryWeakeningTargets.ActualTermRenameAsSubstitution := by
  intro Symbol arity Gamma Delta rho tau q
  exact renameAsSubstitution q Delta rho

theorem actualArgumentRenameAsSubstitution : NumberedPrimaryWeakeningTargets.ActualArgumentRenameAsSubstitution := by
  intro Symbol arity Gamma Delta rho types args
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => exact congrArg₂ AuxArguments.cons (renameAsSubstitution q Delta rho) (ih rest)

theorem packedRenameAsSubstitution {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (rho : Renaming Gamma Delta) (q : Packed Symbol arity Gamma) :
    renamePacked rho q = NumberedPrimarySubstitution.substitutePacked (fun v => AuxTerm.var (rho v)) q := by
  obtain ⟨tau,q⟩ := q
  exact congrArg (fun t => (⟨tau,t⟩ : Packed Symbol arity Delta)) (renameAsSubstitution q Delta rho)

theorem packedWeakeningCancel {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (sigma : Ty) (q : Packed Symbol arity Gamma) :
    NumberedPrimarySubstitution.substitutePacked (singleSubstitution (AuxTerm.bottom sigma))
      (renamePacked (Renaming.weaken Gamma sigma) q) = q := by
  obtain ⟨tau,q⟩ := q
  exact congrArg (fun t => (⟨tau,t⟩ : Packed Symbol arity Gamma))
    (NumberedRewriteApplicationBindingProof.weakeningCancellation Symbol arity Gamma sigma tau q (.bottom sigma))

theorem actualPrimaryWeakening : NumberedPrimaryWeakeningTargets.ActualPrimaryWeakening := by
  intro Symbol arity symbols S Gamma sigma q r
  constructor
  · intro h
    rw [packedRenameAsSubstitution,packedRenameAsSubstitution]
    exact NumberedPrimarySubstitutionProof.actualPrimarySubstitution Symbol arity symbols S Gamma (sigma :: Gamma)
      (fun v => .var (Renaming.weaken Gamma sigma v)) q r h
  · intro h
    have ht := NumberedPrimarySubstitutionProof.actualPrimarySubstitution Symbol arity symbols S (sigma :: Gamma) Gamma
      (singleSubstitution (.bottom sigma)) _ _ h
    simpa only [packedWeakeningCancel] using ht

theorem actualArgumentPrimaryWeakening : NumberedPrimaryWeakeningTargets.ActualArgumentPrimaryWeakening := by
  intro Symbol arity symbols S Gamma sigma types args target
  constructor
  · intro h
    rw [actualArgumentRenameAsSubstitution,actualArgumentRenameAsSubstitution]
    exact NumberedPrimarySubstitutionProof.actualArgumentPrimarySubstitution Symbol arity symbols S Gamma (sigma :: Gamma)
      types (fun v => .var (Renaming.weaken Gamma sigma v)) args target h
  · intro h
    have ht := NumberedPrimarySubstitutionProof.actualArgumentPrimarySubstitution Symbol arity symbols S (sigma :: Gamma) Gamma
      types (singleSubstitution (.bottom sigma)) _ _ h
    simpa only [NumberedRewriteApplicationBindingProof.weakeningArguments] using ht

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningProof
