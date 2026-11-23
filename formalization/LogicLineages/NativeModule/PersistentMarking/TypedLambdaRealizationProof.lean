module

public import LogicLineages.NativeModule.PersistentMarking.TypedLambdaRealizationTargets
public import LogicLineages.NativeModule.PersistentMarking.TypedLambdaRealizationSyntaxProof
import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TypedLambdaRealization
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets

theorem structuralFundamental : StructuralFundamental := by
  intro S
  obtain ⟨wf,lambdaRule⟩ := NativeOrdinalRealizationProof.exact_NativeLambdaRealization S
  refine ⟨wf,?_⟩
  intro C ct cv constants Γ A t
  induction t with
  | var v =>
    intro ρ η environments
    exact ⟨ρ _ v,rfl,environments _ v⟩
  | constant a =>
    intro ρ η _
    exact ⟨ct _ a,rfl,constants _ a⟩
  | @app Γ A D f u ihf ihu =>
    intro ρ η environments
    obtain ⟨F,hF,realizesF⟩ := ihf ρ η environments
    obtain ⟨U,hU,realizesU⟩ := ihu ρ η environments
    refine ⟨(nativeTerms S).app A D F U,?_,realizesF _ U realizesU⟩
    change NativeReduction.app (nativeType A) (nativeType D) F.val U.val =
      NativeReduction.app (nativeType A) (nativeType D)
        (compile ct f (closedEntries ρ)) (compile ct u (closedEntries ρ))
    rw [hF,hU]
  | @lam Γ A D body ih =>
    intro ρ η environments
    let q : (nativeTerms S).term (.arrow A D) :=
      ⟨compile ct (.lam body) (closedEntries ρ),closedCompilation ct (.lam body) ρ⟩
    refine ⟨q,rfl,?_⟩
    apply lambdaRule A D (compile ct body (liftEntries (closedEntries ρ))) q.property
      (fun x => evaluate cv body (extendValues x η))
    intro x u realizesU
    have extended : ∀ B v,
        Realizes (nativeTerms S) wf B (extendTerms u ρ B v) (extendValues x η B v) := by
      intro B v
      cases v with
      | here => exact realizesU
      | there w => exact environments _ w
    obtain ⟨v,hv,realizesV⟩ := ih (extendTerms u ρ) (extendValues x η) extended
    exact ⟨v,hv.trans (closeUnderBinder ct body ρ u).symm,realizesV⟩

theorem pureClosedFundamental : PureClosedFundamental := by
  intro S
  obtain ⟨wf,fundamental⟩ := structuralFundamental S
  refine ⟨wf,?_⟩
  intro A t
  have constants : ∀ B (e : Empty),
      Realizes (nativeTerms S) wf B (emptyConstants S B e) (emptyConstantValues B e) :=
    fun _ e => nomatch e
  have environments : ∀ B (v : Var [] B),
      Realizes (nativeTerms S) wf B (emptyTerms S B v) (emptyValues B v) :=
    fun _ v => nomatch v
  obtain ⟨q,hq,realizesQ⟩ := fundamental (fun _ => Empty) (emptyConstants S) emptyConstantValues
    constants [] A t (emptyTerms S) emptyValues environments
  refine ⟨q,?_,realizesQ⟩
  have envEq : closedEntries (emptyTerms S) = emptyEntries S := by
    funext B v
    exact nomatch v
  rw [envEq] at hq
  exact hq

theorem fullTypedLambdaFragment : FullTypedLambdaFragment :=
  ⟨nativeCompilation,literalSubstitution,structuralFundamental,pureClosedFundamental⟩

#print axioms structuralFundamental
#print axioms pureClosedFundamental
#print axioms fullTypedLambdaFragment

end LogicLineages.PersistentMarking.TypedLambdaRealization
