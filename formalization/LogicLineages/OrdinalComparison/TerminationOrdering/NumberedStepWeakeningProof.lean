module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakeningTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakeningProof
open Source NumberedRewriteSyntax NumberedWindowReduction NumberedStepWeakening NumberedStepRenamingProof

theorem fillerImages (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (sigma : Ty) :
    NonBottomImages (singleSubstitution (retractionFiller Symbol arity Gamma sigma)) := by
  intro tau v
  cases v with
  | here => intro he; cases he
  | there v => intro he; cases he

theorem strictArgumentSubstitution {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma Delta : List Ty} {types : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (hn : NonBottomImages theta)
    {base target : AuxArguments Symbol arity Gamma types}
    (h : WindowArgumentStep Symbol arity symbols S above Gamma types base target) :
    WindowArgumentStep Symbol arity symbols S above Delta types (substituteArguments base theta) (substituteArguments target theta) := by
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest hs => exact .head _ _ _ (substituteStrictStep hs Delta theta hn)
    | tail q rest target hs => exact .tail _ _ _ (ih hs)

theorem actualStepWeakening : NumberedStepWeakeningTargets.ActualStepWeakening := by
  intro Symbol arity symbols S above Gamma sigma tau q r
  constructor
  · exact NumberedStepRenamingProof.actualStepRenaming Symbol arity symbols S above Gamma (sigma :: Gamma) (Renaming.weaken Gamma sigma) tau q r
  · intro h
    have hs := substituteStrictStep h Gamma (singleSubstitution (retractionFiller Symbol arity Gamma sigma))
      (fillerImages Symbol arity Gamma sigma)
    rw [NumberedRewriteApplicationBindingProof.weakeningCancellation Symbol arity Gamma sigma tau q (retractionFiller Symbol arity Gamma sigma),
      NumberedRewriteApplicationBindingProof.weakeningCancellation Symbol arity Gamma sigma tau r (retractionFiller Symbol arity Gamma sigma)] at hs
    exact hs

theorem actualArgumentStepWeakening : NumberedStepWeakeningTargets.ActualArgumentStepWeakening := by
  intro Symbol arity symbols S above Gamma sigma types base target
  constructor
  · exact NumberedStepRenamingProof.actualArgumentStepRenaming Symbol arity symbols S above Gamma (sigma :: Gamma) (Renaming.weaken Gamma sigma) types base target
  · intro h
    have hs := strictArgumentSubstitution (singleSubstitution (retractionFiller Symbol arity Gamma sigma))
      (fillerImages Symbol arity Gamma sigma) h
    simpa only [NumberedRewriteApplicationBindingProof.weakeningArguments] using hs

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakeningProof
