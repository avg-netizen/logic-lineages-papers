module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)

/-- Original object inclusion for two actual observations of the same
literal chosen grammar, with common H/K and both actual weak bounds.
No claim is made about objects not occurring in the actual old outputs. -/
def ExactOpenSelectedGrammarCrossBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d D H K m M old oldTerms oldArgs next nextTerms nextArgs : OTerm α),
  Nonempty (Derivation body Γ (ltF d (suc D))) →
  Nonempty (Derivation body Γ (ltF m (suc M))) →
  Nonempty (Derivation body Γ (observed d H K m old oldTerms oldArgs)) →
  Nonempty (Derivation body Γ (observed D H K M next nextTerms nextArgs)) →
  Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarCrossBoundTargets
