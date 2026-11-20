module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateExplicitCallProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateExplicitTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof (Stable)
open NumberedWindowInternalSparsePositiveIterationCoordinateExplicitCallProof (sameRetained)

attribute [local irreducible] programGraph

abbrev atCall {α : Type} (p : Program 6) (out k prior c ty start cert : OTerm α) : Formula α :=
  programGraph p out (call6 k prior c ty start cert)

/-- The graph cut is typechecked for an abstract program, never by reducing
any actual Program AST or arithmetic graphFormula. -/
theorem moveWithStable (p : Program 6) (safe : Stable p)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out prior c ty k start cert k' start' cert' : OTerm α)
    (known : Nonempty (Derivation body Γ (atCall p out k prior c ty start cert))) :
    Nonempty (Derivation body Γ (atCall p out k' prior c ty start' cert')) :=
  safe body α Γ out (call6 k prior c ty start cert) (call6 k' prior c ty start' cert')
    (sameRetained k prior c ty start cert k' start' cert') known

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateExplicitTransportProof
