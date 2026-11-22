module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalClosedPrograms (allBlock)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverSelectedSuccessorTargets (termProjection argsProjection)
open NumberedWindowInternalCoverSelectedGrammarTargets (grammarReport)

/-- One actual state and both actual reads of that very state. -/
abbrev observed {α : Type} (d H K M state terms args : OTerm α) : Formula α :=
  grammarReport state d H K M ⊓ (termProjection terms state ⊓ argsProjection args state)

abbrev observationMatrix {α : Type} (d H K M : OTerm α) : Formula (α ⊕ Fin 3) :=
  observed (d.relabel Sum.inl) (H.relabel Sum.inl) (K.relabel Sum.inl) (M.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

abbrev existingObservation {α : Type} (d H K M : OTerm α) : Formula α :=
  block (observationMatrix d H K M)

abbrev pairInclusion {α : Type} (loTerms hiTerms loArgs hiArgs : OTerm α) : Formula α :=
  axisInclusion loTerms hiTerms ⊓ axisInclusion loArgs hiArgs

abbrev compared {α : Type} (d H K m M : OTerm α) (w : Fin 6 → OTerm α) : Formula α :=
  (observed d H K m (w 0) (w 1) (w 2) ⊓ observed d H K M (w 3) (w 4) (w 5)).imp
    (pairInclusion (w 1) (w 4) (w 2) (w 5))

abbrev widthMatrix {α : Type} (d H K m M : OTerm α) : Formula (α ⊕ Fin 6) :=
  compared (d.relabel Sum.inl) (H.relabel Sum.inl) (K.relabel Sum.inl)
    (m.relabel Sum.inl) (M.relabel Sum.inl) (fun i => .var (.inr i))

/-- The actual object motive sees arbitrary genuine reports at the same
depth. It does not assume equality of the two width-parametrized states. -/
abbrev widthAt {α : Type} (d H K m M : OTerm α) : Formula α :=
  allBlock (widthMatrix d H K m M)

abbrev widthMotive {α : Type} (H K m M : OTerm α) : Formula (α ⊕ Fin 1) :=
  widthAt (.var (.inr 0)) (H.relabel Sum.inl) (K.relabel Sum.inl)
    (m.relabel Sum.inl) (M.relabel Sum.inl)

def ExactOpenSelectedGrammarWidth : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K m M old oldTerms oldArgs next nextTerms nextArgs : OTerm α),
  Nonempty (Derivation body Γ (ltF m (suc M))) →
  Nonempty (Derivation body Γ (observed d H K m old oldTerms oldArgs)) →
  Nonempty (Derivation body Γ (observed d H K M next nextTerms nextArgs)) →
  Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
