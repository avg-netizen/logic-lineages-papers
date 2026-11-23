module

public import LogicLineages.NativeModule.PersistentMarking.TypedLambdaRealizationDefinitions

@[expose] public section

namespace LogicLineages.PersistentMarking.TypedLambdaRealization
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets NativeTowerSyntaxProof

/-- Every grammar term compiles to the existing typed, ordinary, free-name-closed
native syntax in any target binder context fitting its entries. -/
def NativeCompilation : Prop :=
  ∀ (S : Signature) (C : FiniteType → Type) (c : ConstantTerms S C)
    (Γ : List FiniteType) (A : FiniteType) (t : Term C Γ A)
    (Δ : BoundContext) (ρ : EntryEnv S Γ),
    EnvFits Δ ρ → NativeIn S Δ (compile c t ρ) (nativeType A)

/-- Exact compatibility with the actual `Spine.substitute` operation, including
arbitrarily nested binders and insertion of closed native arguments. -/
def LiteralSubstitution : Prop :=
  ∀ (S : Signature) (C : FiniteType → Type) (c : ConstantTerms S C)
    (Γ : List FiniteType) (A : FiniteType) (t : Term C Γ A)
    (B : FiniteType) (u : (nativeTerms S).term B) (depth : Nat)
    (ρ σ : EntryEnv S Γ), EnvSub u depth ρ σ →
    substitute (.cons u.val .nil) depth (compile c t ρ) = compile c t σ

/-- Structural fundamental lemma for the complete typed lambda/application
grammar. Only constant and variable realizations are premises; realization of
lambda bodies must follow from the syntax induction. -/
def StructuralFundamental : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (C : FiniteType → Type) (ct : ConstantTerms S C) (cv : ConstantValues C),
      (∀ A a, Realizes (nativeTerms S) wf A (ct A a) (cv A a)) →
      ∀ (Γ : List FiniteType) (A : FiniteType) (t : Term C Γ A)
        (ρ : TermEnv S Γ) (η : ValueEnv Γ),
        (∀ B v, Realizes (nativeTerms S) wf B (ρ B v) (η B v)) →
        ∃ q : (nativeTerms S).term A,
          q.val = compile ct t (closedEntries ρ) ∧
          Realizes (nativeTerms S) wf A q (evaluate cv t η)

/-- The closed pure lambda/application fragment needs no interpretation or
realization premise: its ordinary native compilation realizes its denotation. -/
def PureClosedFundamental : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (A : FiniteType) (t : Term (fun _ => Empty) [] A),
      ∃ q : (nativeTerms S).term A,
        q.val = compile (emptyConstants S) t (emptyEntries S) ∧
        Realizes (nativeTerms S) wf A q (evaluate emptyConstantValues t emptyValues)

def FullTypedLambdaFragment : Prop :=
  NativeCompilation ∧ LiteralSubstitution ∧ StructuralFundamental ∧ PureClosedFundamental

end LogicLineages.PersistentMarking.TypedLambdaRealization
