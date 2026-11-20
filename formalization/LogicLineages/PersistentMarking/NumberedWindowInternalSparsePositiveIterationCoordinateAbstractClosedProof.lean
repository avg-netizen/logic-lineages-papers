module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateAbstractTransportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateAbstractClosedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof (Stable)
open NumberedWindowInternalSparsePositiveIterationCoordinateAbstractTransportProof (atCall moveWithStable)

attribute [local irreducible] programGraph

theorem closedWithStable (p : Program 6) (safe : Stable p)
    (body : Positive (Fin 1)) (α : Type)
    (out prior c ty k start cert k' start' cert' : OTerm α) :
    let a := atCall p out k prior c ty start cert
    let b := atCall p out k' prior c ty start' cert'
    Nonempty (Derivation body [] ((a.imp b) ⊓ (b.imp a))) := by
  let a := atCall p out k prior c ty start cert
  let b := atCall p out k' prior c ty start' cert'
  have ha : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body [b] b := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := moveWithStable p safe body α [a] out prior c ty k start cert k' start' cert' ⟨ha⟩
  obtain ⟨backward⟩ := moveWithStable p safe body α [b] out prior c ty k' start' cert' k start cert ⟨hb⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateAbstractClosedProof
