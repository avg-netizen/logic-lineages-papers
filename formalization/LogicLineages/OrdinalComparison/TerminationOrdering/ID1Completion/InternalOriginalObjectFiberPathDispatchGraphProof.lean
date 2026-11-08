module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchGraphProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalObjectFiberPathDispatch InternalOriginalObjectFiberPathDispatchSupportProof
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSupportProof InternalAcceptanceBranchProof
open InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof

theorem actualInternalOriginalObjectFiberPairGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberPairGraph := by
  intro Gamma body α Delta argumentObject argument
  obtain ⟨hf⟩ := InternalUnpairProof.actualOriginalGeneratedCodeInverse body α
    argumentObject (numeral (Encodable.encode Gamma)) argument
  obtain ⟨hb⟩ := InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body α
    argumentObject (numeral (Encodable.encode Gamma)) argument
  exact ⟨Derivation.conjunctionIntroduction (weakenClosed hf Delta) (weakenClosed hb Delta)⟩

theorem actualInternalOriginalObjectFiberActiveGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberActiveGraph := by
  intro Gamma vertexProgram oldLift body α Delta context domain codomain argumentObject argument certificate out
  let a := fiberCoordinates Gamma argumentObject argument
  let g := dispatchGraph Gamma vertexProgram oldLift out context domain codomain argumentObject certificate
  let f := InternalApplicationPathMap.mapGraph vertexProgram out certificate context domain codomain argument
  obtain ⟨hf⟩ := dispatchRecover (body := body) (Delta := g :: a :: Delta)
    Gamma vertexProgram oldLift context domain codomain argumentObject argument certificate out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := dispatchAccept (body := body) (Delta := f :: a :: Delta)
    Gamma vertexProgram oldLift context domain codomain argumentObject argument certificate out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualInternalOriginalObjectFiberZeroGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberZeroGraph := by
  intro Gamma vertexProgram oldLift body α Delta context domain codomain argumentObject certificate out
  obtain ⟨h⟩ := actualOriginalZeroBranch body 5 (fiberTest Gamma) oldLift (activeBranch vertexProgram)
    α out (arguments context domain codomain argumentObject certificate)
  exact ⟨weakenClosed h Delta⟩

theorem actualInternalOriginalObjectFiberNonmatchGraph :
    InternalOriginalObjectFiberPathDispatchTargets.ActualInternalOriginalObjectFiberNonmatchGraph := by
  intro Gamma vertexProgram oldLift body α Delta context domain codomain argumentObject leftCode certificate out
  let a := graph1 InternalUnpair.left leftCode argumentObject ⊓
    (InternalControlGraph.equal leftCode (numeral (Encodable.encode Gamma))).not
  have ha : Nonempty (Derivation body (a :: Delta) a) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hz⟩ := fiberTestReject Gamma (arguments context domain codomain argumentObject certificate)
    leftCode (andLeft ha) (andRight ha)
  obtain ⟨hi⟩ := actualInternalOriginalObjectFiberZeroGraph Gamma vertexProgram oldLift body α
    (a :: Delta) context domain codomain argumentObject certificate out
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hi hz)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchGraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchGraphProof
