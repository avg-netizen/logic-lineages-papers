module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowTraces NumberedPrimaryWeakening
open NumberedStepRenamingProof NumberedPrimarySubstitution NumberedStepWeakening

theorem strictTrace {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma Delta : List Ty} (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (hn : NonBottomImages theta) {count : Nat} {q r : Packed Symbol arity Gamma}
    (h : WindowTrace Symbol arity symbols S above Gamma count q r) :
    WindowTrace Symbol arity symbols S above Delta count (substitutePacked theta q) (substitutePacked theta r) := by
  induction h with
  | equivalent he => exact .equivalent (NumberedPrimarySubstitutionProof.substitutePrimary he Delta theta)
  | raw q r hs => exact .raw _ _ (substituteStrictStep hs Delta theta hn)
  | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2

theorem strictTupleTrace {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma Delta : List Ty} (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (hn : NonBottomImages theta) {types : List Ty} {count : Nat} {base target : AuxArguments Symbol arity Gamma types}
    (h : WindowTupleTrace Symbol arity symbols S above Gamma types count base target) :
    WindowTupleTrace Symbol arity symbols S above Delta types count (substituteArguments base theta) (substituteArguments target theta) := by
  induction h with
  | equivalent he => exact .equivalent (NumberedPrimarySubstitutionProof.actualArgumentPrimarySubstitution
      Symbol arity symbols S Gamma Delta _ theta _ _ he)
  | raw hs => exact .raw (NumberedStepWeakeningProof.strictArgumentSubstitution theta hn hs)
  | trans h1 h2 ih1 ih2 => exact .trans ih1 ih2

theorem packedCancel {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} (sigma : Ty) (q : Packed Symbol arity Gamma) :
    substitutePacked (singleSubstitution (retractionFiller Symbol arity Gamma sigma))
      (renamePacked (Renaming.weaken Gamma sigma) q) = q := by
  obtain ⟨tau,q⟩ := q
  exact congrArg (fun t => (⟨tau,t⟩ : Packed Symbol arity Gamma))
    (NumberedRewriteApplicationBindingProof.weakeningCancellation Symbol arity Gamma sigma tau q (retractionFiller Symbol arity Gamma sigma))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceWeakeningSupportProof
