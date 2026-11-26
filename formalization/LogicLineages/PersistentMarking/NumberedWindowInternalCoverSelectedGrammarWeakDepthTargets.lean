module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (allOne)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets (depthAt)

abbrev depthGuard {α : Type} (d D H K M : OTerm α) : Formula α :=
  (ltF d (suc D)).imp (depthAt d D H K M)

abbrev lowerMatrix {α : Type} (D H K M : OTerm α) : Formula (α ⊕ Fin 1) :=
  depthGuard (.var (.inr 0)) (D.relabel Sum.inl) (H.relabel Sum.inl) (K.relabel Sum.inl) (M.relabel Sum.inl)

abbrev allLower {α : Type} (D H K M : OTerm α) : Formula α :=
  allOne (lowerMatrix D H K M)

/-- Upper depth alone is inducted. The object lower depth and all six
genuine observed report outputs are bound inside this motive. -/
abbrev upperMotive {α : Type} (H K M : OTerm α) : Formula (α ⊕ Fin 1) :=
  allLower (.var (.inr 0)) (H.relabel Sum.inl) (K.relabel Sum.inl) (M.relabel Sum.inl)

def ExactOpenSelectedGrammarWeakDepth : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d D H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α),
  Nonempty (Derivation body Γ (ltF d (suc D))) →
  Nonempty (Derivation body Γ (observed d H K M old oldTerms oldArgs)) →
  Nonempty (Derivation body Γ (observed D H K M next nextTerms nextArgs)) →
  Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
