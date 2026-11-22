module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm measurePair)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport freePart boundPart)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)

/-- The two literal named branches and their original tags. -/
def selectedNamedPart (b : Bool) : Program 5 := if b then boundPart else freePart

def OpenSelectedPartContainsNamedLeaf (b : Bool) (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args ty i : OTerm α),
    Nonempty (Derivation body Γ (stepReport P out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph ids i)) →
    Nonempty (Derivation body Γ (memberGraph out (namedTerm b.toNat ty i)))

/-- The named key is admissible in the actual numeral range when the
original object comparison has right endpoint successor of width. -/
def ExactOpenSelectedGrammarNamedLeafAtSuccessor : Prop :=
  ∀ (b : Bool) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K width next out args ty i : OTerm α),
    Nonempty (Derivation body Γ (observed (suc d) H K width next out args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (ltF i (suc width))) →
    Nonempty (Derivation body Γ (memberGraph out (namedTerm b.toNat ty i)))

/-- A literal named leaf is in its actual selected physical scratch.
The actual width bound relates to the same measured numeral coordinate. -/
def ExactOpenSelectedGrammarNamedLeafScratch : Prop :=
  ∀ (b : Bool) (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (m d width vertices ty i : OTerm α),
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (ltF i (suc width))) →
    Nonempty (Derivation body Γ (unary V (suc z) (namedTerm b.toNat ty i))) →
    Nonempty (Derivation body Γ (unary Measure m (namedTerm b.toNat ty i))) →
    Nonempty (Derivation body Γ (measurePair m d width)) →
    Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s)
      vertices (namedTerm b.toNat ty i))) →
    Nonempty (Derivation body Γ (memberGraph vertices (namedTerm b.toNat ty i)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafTargets
