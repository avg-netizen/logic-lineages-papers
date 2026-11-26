module

public import LogicLineages.NativeModule.PersistentMarking.NativeRealizationChainTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeLambdaChain
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication OrdinalRealizationTargets NativeOrdinalRealizationTargets

/-- The whole argument of the last sentence of the printed proof of
`lem:realization`, as one statement: if every closed substituted body
instance of a closed native lambda realizes the corresponding value of `f`,
then every term that reaches that lambda through a finite nonempty chain of
strict edges realizes `f`. (The lambda itself is #1447's abstraction rule;
the chain is #1450.) This is not a structural fundamental lemma over all
typed native terms. -/
def NativeLambdaChainRealization : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (A D : FiniteType) (body : Expr)
      (hl : ClosedNative S (.lam (actualType (nativeShape A)) body)
        (.arrow (actualType (nativeShape A)) (actualType (nativeShape D))))
      (f : Value A → Value D) (s : (nativeTerms S).term (.arrow A D)),
      (∀ (x : Value A) (u : (nativeTerms S).term A), Realizes (nativeTerms S) wf A u x →
        ∃ v : (nativeTerms S).term D, v.val = substitute (.cons u.val .nil) 0 body ∧
          Realizes (nativeTerms S) wf D v (f x)) →
      Relation.TransGen (fun a b => (nativeTerms S).below (.arrow A D) a b)
        (⟨.lam (actualType (nativeShape A)) body, hl⟩ : (nativeTerms S).term (.arrow A D)) s →
      Realizes (nativeTerms S) wf (.arrow A D) s f

end LogicLineages.PersistentMarking.NativeLambdaChain
