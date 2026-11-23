module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalRealizationTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRealizationChain
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication OrdinalRealizationTargets NativeOrdinalRealizationTargets

/-- Realization is transported backward along every finite nonempty chain
of strict edges: the transitive closure of the term structure's strict
relation. This is the sentence "an induction on the number of beta steps
permits any finite sequence" in the printed proof of `lem:realization`. -/
def RealizationChainBackward (terms : TermStructure) (wf : WellFounded (terms.below .base)) : Prop :=
  ∀ A (s t : terms.term A) (v : Value A),
    Relation.TransGen (fun a b => terms.below A a b) t s →
      Realizes terms wf A t v → Realizes terms wf A s v

/-- For every term structure, single-edge backward transport gives
finite-chain backward transport. -/
def ExactChainOfStrict : Prop :=
  ∀ (terms : TermStructure) (wf : WellFounded (terms.below .base)),
    RealizationStrictBackward terms wf → RealizationChainBackward terms wf

/-- On the closed native terms with their strict relation. -/
def NativeRealizationFiniteChains : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    RealizationChainBackward (nativeTerms S) wf

end LogicLineages.PersistentMarking.NativeRealizationChain
