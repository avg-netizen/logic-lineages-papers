module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeRealizationChainTargets
public import LogicLineages.NativeModule.PersistentMarking.TypedLambdaRealizationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRealizationComplete

/-- Paper 16's realization closure and the structural fundamental lemma for its
finite-semantic-type lambda/application fragment, with the exact native syntax
and substitution bridge. Finite strict-chain transport also retains the final
sentence of the printed proof. Constant/environment realization hypotheses are
the ordinary interpretation hypotheses inside the structural theorem; lambda
body realization is proved by induction, not supplied as an extra assumption. -/
def FullRealization : Prop :=
  NativeOrdinalRealizationTargets.NativeRealizationClosure ∧
  TypedLambdaRealization.FullTypedLambdaFragment ∧
  NativeRealizationChain.NativeRealizationFiniteChains

end LogicLineages.PersistentMarking.NativeRealizationComplete
