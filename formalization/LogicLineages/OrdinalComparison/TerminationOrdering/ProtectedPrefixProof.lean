module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open ProtectedPrefix

 theorem literalMask : ProtectedPrefixTargets.LiteralMask := by
  intro pre Gamma
  induction pre with
  | nil =>
    constructor
    · intro tau v
      cases v
    · intro tau v
      rfl
  | cons sigma pre ih =>
    constructor
    · intro tau v
      cases v with
      | here => rfl
      | there v => exact ih.1 v
    · intro tau v
      exact ih.2 v

theorem oldNameLift : ProtectedPrefixTargets.OldNameLift := by
  intro Symbol arity Gamma Delta pre s tau v
  induction pre with
  | nil =>
    exact (SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Delta tau (s v)).symm
  | cons sigma pre ih =>
    change renameTerm (liftFree pre s (freeRename pre Gamma v)) (Renaming.weaken _ sigma)=_
    rw [ih,RenamingEquivarianceBindingProof.renameComposition]
    rfl

theorem closingOldName : ProtectedPrefixTargets.ClosingOldName := by
  intro Symbol arity Delta pre consumed tau v
  induction pre with
  | nil => cases consumed; rfl
  | cons sigma pre ih =>
    cases consumed with
    | cons a rest => exact ih rest

theorem raisedSourceClosing : ProtectedPrefixTargets.RaisedSourceClosing := by
  intro Symbol arity Delta pre consumed tau q
  have H := RenamingEquivarianceBindingProof.substitutionCovariance Symbol arity
    Delta (pre++Delta) Delta Delta tau q (freeRename pre Delta) (fun v => v)
    (fun v => .var v) (closePrefix consumed)
    (fun {_} v => closingOldName Symbol arity Delta pre consumed _ v)
  rw [SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Delta tau q,
    SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Delta tau q] at H
  exact H

theorem raisedSourceApplication : ProtectedPrefixTargets.RaisedSourceApplication := by
  intro Symbol arity Delta pre consumed sigma tau types q args h
  have H := RenamingEquivarianceApplicationProof.originalApplyCovariance Symbol arity
    Delta (pre++Delta) Delta Delta sigma tau types q args (freeRename pre Delta) (fun v => v)
    (fun v => .var v) (closePrefix consumed) h
    (fun {_} v => closingOldName Symbol arity Delta pre consumed _ v)
  rw [SourceMarkedBindingProof.markedRenamingIdentity.2 Symbol arity Delta types args] at H
  apply H.trans
  cases ha : applyOriginalWith q (fun v => .var v) args h with
  | none => rfl
  | some out =>
    exact congrArg some (SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Delta tau out)

theorem originalVariableBlocked : ProtectedPrefixTargets.OriginalVariableBlocked := by
  intro Symbol arity Delta pre consumed sigma tau v types args h hn
  cases args with
  | nil => exact False.elim (hn rfl)
  | cons a rest => rfl

theorem literalBinderStep : ProtectedPrefixTargets.LiteralBinderStep := by
  intro Symbol arity Gamma Delta pre s consumed sigma tau rest body a args
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefixProof
