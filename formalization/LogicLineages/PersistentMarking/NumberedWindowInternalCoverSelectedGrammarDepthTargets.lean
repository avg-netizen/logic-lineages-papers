module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)

/-- Common H,K,M, arbitrary reported coding values. Keeping the two
depth positions explicit here is a syntax aid, not a transport theorem. -/
abbrev depthCompared {α : Type} (d D H K M : OTerm α) (w : Fin 6 → OTerm α) : Formula α :=
  (observed d H K M (w 0) (w 1) (w 2) ⊓ observed D H K M (w 3) (w 4) (w 5)).imp
    (pairInclusion (w 1) (w 4) (w 2) (w 5))

abbrev depthMatrix {α : Type} (d D H K M : OTerm α) : Formula (α ⊕ Fin 6) :=
  depthCompared (d.relabel Sum.inl) (D.relabel Sum.inl) (H.relabel Sum.inl)
    (K.relabel Sum.inl) (M.relabel Sum.inl) (fun i => .var (.inr i))

abbrev depthAt {α : Type} (d D H K M : OTerm α) : Formula α :=
  allBlock (depthMatrix d D H K M)

abbrev adjacentAt {α : Type} (d H K M : OTerm α) : Formula α :=
  depthAt d (suc d) H K M

abbrev adjacentMotive {α : Type} (H K M : OTerm α) : Formula (α ⊕ Fin 1) :=
  adjacentAt (.var (.inr 0)) (H.relabel Sum.inl) (K.relabel Sum.inl) (M.relabel Sum.inl)

def ExactOpenSelectedGrammarAdjacentDepth : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α),
  Nonempty (Derivation body Γ (observed d H K M old oldTerms oldArgs)) →
  Nonempty (Derivation body Γ (observed (suc d) H K M next nextTerms nextArgs)) →
  Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
