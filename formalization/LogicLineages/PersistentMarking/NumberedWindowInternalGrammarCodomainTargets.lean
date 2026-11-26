module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCell

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets (GrammarCodomainInversion)

/-- Explicit finite numerical closure under the original sparse-cell tail
program, tested at every listed numeral. This is not an internal inversion
rule and is not asserted for arbitrary Settings values. -/
def FiniteCodomainClosure (codes : List Nat) : Prop :=
  ∀ code ∈ codes, evaluate cellTail (code ::ᵥ nil) ∈ codes

/-- A derivable original-calculus implication for arbitrary open arrow fields
from finite numeric closure. The actual cellTail graph at rawCons dom cod
supplies the codomain; no numeric reflection at those open fields is used. -/
def ExactOpenFiniteGrammarCodomain : Prop :=
  ∀ (s : Settings), FiniteCodomainClosure s.types →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom cod : OTerm α),
      Nonempty (Derivation body Γ
        ((literalMembership s.types (rawCons dom cod)).imp (literalMembership s.types cod)))

/-- The missing original grammar-codomain rule of #1461 follows from the
finite closure above. The all-type program's separate inversion remains open. -/
def ExactFiniteGrammarCodomainInversion : Prop :=
  ∀ (s : Settings), FiniteCodomainClosure s.types →
    ∀ (body : Positive (Fin 1)), GrammarCodomainInversion body s

end LogicLineages.PersistentMarking.NumberedWindowInternalGrammarCodomainTargets
