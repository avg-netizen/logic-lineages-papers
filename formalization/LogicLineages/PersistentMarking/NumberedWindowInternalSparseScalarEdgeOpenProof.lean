module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenProjectionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseScalarEdge
open NumberedWindowInternalSparseScalarEdgeTargets
open NumberedWindowInternalSparseScalarEdgeOpenProjectionProof (projectTwo projectThree)

attribute [local irreducible] programGraph

/-- Both directions borrow only the genuine graph rules for the actual
composition and exact-one conjunctions, never the numeric calibration. -/
theorem graph : ExactOpenPackedScalarEdge := by
  intro X W body α Γ ctx ty w v
  let xs : Fin 4 → OTerm α := edgeTape ctx ty w v
  let ex := exchangeCall X
  let ws := sourceWindow W
  let wt := targetWindow W
  let both := conjunction ws wt
  let accepted := edgeGraph X W ctx ty w v
  let calls := edgeCalls X W ctx ty w v
  have toCalls : Nonempty (Derivation body (accepted :: Γ) calls) := by
    let Δ := accepted :: Γ
    have known : Nonempty (Derivation body Δ accepted) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨outer⟩ := conjunctionRecover ex both xs known
    obtain ⟨inner⟩ := conjunctionRecover ws wt xs ⟨Derivation.conjunctionRight outer⟩
    obtain ⟨a⟩ := (projectTwo (body := body) (Γ := Δ) X 2 3 xs).mp
      ⟨Derivation.conjunctionLeft outer⟩
    obtain ⟨b⟩ := (projectThree (body := body) (Γ := Δ) W 0 1 2 xs).mp
      ⟨Derivation.conjunctionLeft inner⟩
    obtain ⟨c⟩ := (projectThree (body := body) (Γ := Δ) W 0 1 3 xs).mp
      ⟨Derivation.conjunctionRight inner⟩
    exact ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b c)⟩
  have toGraph : Nonempty (Derivation body (calls :: Γ) accepted) := by
    let Δ := calls :: Γ
    have known : Derivation body Δ calls := Derivation.hypothesis List.mem_cons_self
    have inner := Derivation.conjunctionRight known
    have a := (projectTwo (body := body) (Γ := Δ) X 2 3 xs).mpr
      ⟨Derivation.conjunctionLeft known⟩
    have b := (projectThree (body := body) (Γ := Δ) W 0 1 2 xs).mpr
      ⟨Derivation.conjunctionLeft inner⟩
    have c := (projectThree (body := body) (Γ := Δ) W 0 1 3 xs).mpr
      ⟨Derivation.conjunctionRight inner⟩
    exact conjunctionAccept ex both xs a (conjunctionAccept ws wt xs b c)
  obtain ⟨forward⟩ := toCalls
  obtain ⟨backward⟩ := toGraph
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenProof
