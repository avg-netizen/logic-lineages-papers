module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalObjectFiberCertifiedLiftTargets InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof
open InternalApplicationStepPeelSupportProof InternalTagArithmeticSupportProof

 theorem actualInternalOriginalObjectFunctionFiber : ActualInternalOriginalObjectFunctionFiber := by
  intro K Gamma p body α Delta f a
  obtain ⟨h⟩ := functionFiber (body := body) K Gamma p f a
    (andLeft ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩)
    (andRight ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

 theorem actualInternalOriginalObjectTargetFiber : ActualInternalOriginalObjectTargetFiber := by
  intro K Gamma p body α Delta f g witness
  obtain ⟨h⟩ := targetFiber (body := body) K Gamma p f g witness
    (andLeft ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩)
    (andRight ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

 theorem actualInternalOriginalObjectFiberTypedGraph : ActualInternalOriginalObjectFiberTypedGraph := by
  intro K Gamma p body α Delta tau object payload
  let c := InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload
  let t := InternalComputabilityApplication.typed (InternalOriginalObjectFiberSourceAssembly.comp K Gamma p) tau
    (SourceComputabilityFormulaSupportProof.numeral K) object
  let r := InternalOriginalObjectFiberCertifiedLift.rawTyped p tau payload
  have hc : Derivation body (c :: Delta) c := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hf⟩ := typedRecover K Gamma p tau object payload ⟨InternalBetaTotalityProof.addHyp hc t⟩
    (show Nonempty (Derivation body (t :: c :: Delta) t) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := typedAccept K Gamma p tau object payload ⟨InternalBetaTotalityProof.addHyp hc r⟩
    (show Nonempty (Derivation body (r :: c :: Delta) r) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

 theorem actualInternalOriginalObjectFiberPositiveRecovery : ActualInternalOriginalObjectFiberPositiveRecovery := by
  intro K Gamma p body α Delta f g x y witness
  obtain ⟨h⟩ := positiveRecover (body := body) K Gamma p f g x y witness
    (andLeft (andLeft ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩))
    (andRight (andLeft ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩))
    (andRight ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

 theorem actualInternalOriginalObjectFiberPositiveReconstruction : ActualInternalOriginalObjectFiberPositiveReconstruction := by
  intro K Gamma p hw body α Delta tau out other lifted rawOut rawOther
  obtain ⟨h⟩ := positiveAccept (body := body) K Gamma p hw tau out other lifted rawOut rawOther
    ⟨Derivation.hypothesis (List.mem_cons_self (l := Delta))⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperProof
