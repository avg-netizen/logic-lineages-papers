module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportSubstitutionProof
open Source NumberedRewriteSyntax NumberedRenamingSupport

theorem liftedEnvironment {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {sigma : Ty}
    (P : VariablePredicate Gamma) (Q : VariablePredicate Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (h : ∀ {tau : Ty} (v : Variable Gamma tau), P v → supports Q (theta v)) :
    ∀ {tau : Ty} (v : Variable (sigma :: Gamma) tau), liftPredicate P v →
      supports (liftPredicate Q) (liftSubstitution theta v) := by
  intro tau v hv
  cases v with
  | here => trivial
  | there v =>
    exact (NumberedSupportPullbackProof.actualTermSupportPullback Symbol arity Delta (sigma :: Delta)
      (Renaming.weaken Delta sigma) (liftPredicate Q) tau (theta v)).mpr (h v hv)

theorem supportSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta : List Ty) (P : VariablePredicate Gamma) (Q : VariablePredicate Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta), supports P q →
    (∀ {upsilon : Ty} (v : Variable Gamma upsilon), P v → supports Q (theta v)) → supports Q (substitute q theta) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (P : VariablePredicate Gamma) (Q : VariablePredicate Delta)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta), supportsArguments P args →
      (∀ {upsilon : Ty} (v : Variable Gamma upsilon), P v → supports Q (theta v)) → supportsArguments Q (substituteArguments args theta))
  case var v => intro Delta P Q theta hq he; exact he v hq
  case lam body ih =>
    intro Delta P Q theta hq he
    exact ih _ (liftPredicate P) (liftPredicate Q) (liftSubstitution theta) hq (liftedEnvironment P Q theta he)
  case app f a ihf iha => intro Delta P Q theta hq he; exact ⟨ihf Delta P Q theta hq.1 he,iha Delta P Q theta hq.2 he⟩
  case bottom => intros; trivial
  case ordinary f base ih => intro Delta P Q theta hq he; exact ih Delta P Q theta hq he
  case numbered k f tau base types extras ihb ihe =>
    intro Delta P Q theta hq he
    exact ⟨ihb Delta P Q theta hq.1 he,ihe Delta P Q theta hq.2 he⟩
  case nil => intros; trivial
  case cons Gamma sigma types q rest ihq ihr Delta P Q theta hq he =>
    exact ⟨ihq Delta P Q theta hq.1 he,ihr Delta P Q theta hq.2 he⟩

theorem actualTermSupportSubstitution : NumberedSupportSubstitutionTargets.ActualTermSupportSubstitution := by
  intro Symbol arity Gamma Delta P Q theta tau q hq he
  exact supportSubstitute q Delta P Q theta hq he

theorem actualArgumentSupportSubstitution : NumberedSupportSubstitutionTargets.ActualArgumentSupportSubstitution := by
  intro Symbol arity Gamma Delta P Q theta types args hq he
  induction types with
  | nil => cases args; trivial
  | cons tau types ih => cases args with
    | cons q rest => exact ⟨supportSubstitute q Delta P Q theta hq.1 he,ih rest hq.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportSubstitutionProof
