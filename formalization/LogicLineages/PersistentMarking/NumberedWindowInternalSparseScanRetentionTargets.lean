module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedFilter (cell)

/-- The genuine row has output exactly one iff the head is the candidate,
the directed edge from that head accepts, or the actual previous result is one. -/
def ExactScanRowBranches : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (h prev ctx ty k : OTerm α),
    let row := programGraph (scanStep E) (suc z) (rowTape h prev ctx ty k)
    let hits := eqn h k ⊔ (acceptEdge E ctx ty h k ⊔ eqn prev (suc z))
    Nonempty (Derivation body Γ ((row.imp hits) ⊓ (hits.imp row)))

/-- The scan on actual cons is successful exactly when that head matches,
its directed edge accepts, or the actual scan of this tail succeeds. -/
def ExactScanOnCons : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (seen h tail ctx ty k : OTerm α),
    let test := scanGraph E seen ctx ty k
    let hits := eqn h k ⊔ (acceptEdge E ctx ty h k ⊔ scanGraph E tail ctx ty k)
    Nonempty (Derivation body Γ ((cell seen h tail).imp ((test.imp hits) ⊓ (hits.imp test))))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanRetentionTargets
