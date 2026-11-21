module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseRawRunLiftChecks (exact_OpenLiftedOwnRun)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets

/-- Real selected child acceptance gives the original own-run graph.
Only the supplied new four calls re-establish the wrapped typed graph. -/
theorem wrap {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (root other windowProg : Program 3) (syntaxProg : Program 1)
    (ctx dom cod arg source child dest : OTerm α)
    (known : Nonempty (Derivation body Γ
      (liftInputs root other windowProg syntaxProg ctx dom cod arg source child dest))) :
    Nonempty (Derivation body Γ
      (programGraph (typedRaw5 root other windowProg syntaxProg) (suc z)
        ![ctx,cod,auxiliaryTerm dom cod source arg,functionWitnessTerm child,auxiliaryTerm dom cod dest arg])) := by
  let src := auxiliaryTerm dom cod source arg
  let wr := functionWitnessTerm child
  let dst := auxiliaryTerm dom cod dest arg
  obtain ⟨premise⟩ := known
  obtain ⟨before⟩ := exact_OpenTypedRaw5 body root other windowProg syntaxProg α Γ
    ctx (rawCons dom cod) source child dest
  have childFacts := Derivation.implicationElimination (Derivation.conjunctionLeft before)
    (Derivation.conjunctionLeft premise)
  obtain ⟨liftedRun⟩ := closedApply
    (exact_OpenLiftedOwnRun body root other α dom cod arg source child dest z)
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft childFacts)⟩
  have guards : Derivation body Γ (liftedEndpointGuards windowProg syntaxProg ctx cod src dst) :=
    Derivation.conjunctionRight premise
  obtain ⟨after⟩ := exact_OpenTypedRaw5 body root other windowProg syntaxProg α Γ ctx cod src wr dst
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight after)
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft guards) liftedRun)
      (Derivation.conjunctionRight guards))⟩

theorem liftGraph : ExactOpenTypedRaw5FunctionLift := by
  intro body root other windowProg syntaxProg α Γ ctx dom cod arg source child dest
  let a := liftInputs root other windowProg syntaxProg ctx dom cod arg source child dest
  obtain ⟨d⟩ := wrap (body := body) (Γ := a :: Γ) root other windowProg syntaxProg
    ctx dom cod arg source child dest ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftGraphProof
