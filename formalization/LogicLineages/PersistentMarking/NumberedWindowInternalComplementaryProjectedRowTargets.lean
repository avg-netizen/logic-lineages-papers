module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginRowsFilterTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep rowCell Report)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)

def outcomes {α : Type} (row tailL tailR outL outR : OTerm α) : Formula α :=
  (rowCell outL row tailL ⊓ eqn outR tailR) ⊔ (eqn outL tailL ⊓ rowCell outR row tailR)

def ExactOpenComplementaryProjectedRow : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (row pool key tailL tailR outL outR : OTerm α),
    Report B Γ (unary (field 1) key row) →
    Report B Γ (programGraph (rowStep true) outL ![row,tailL,pool]) →
    Report B Γ (programGraph (rowStep false) outR ![row,tailR,pool]) →
    Report B Γ (outcomes row tailL tailR outL outR)

end LogicLineages.PersistentMarking.NumberedWindowInternalComplementaryProjectedRowTargets
