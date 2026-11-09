module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalParameterizedQuotientEdgeChecker InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof InternalGraphCompositionFunctionalityProof
open InternalOriginalUniformDescentSelection (Data)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem fieldValue (selector : Program 1) (value : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 selector value (xs 2)))) :
    Nonempty (Derivation body Gamma (programGraph (field selector) value xs)) :=
  unaryValue selector (.projection 2) value (xs 2) xs h (projectionValue 2 xs)

theorem representativeAtValue (representative : Program 2) (selector : Program 1)
    (raw value : OTerm α) (xs : Fin 4 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hr : Nonempty (Derivation body Gamma (graph2 representative value raw (xs 3)))) :
    Nonempty (Derivation body Gamma (programGraph (representativeAt representative selector) value xs)) :=
  binaryValue representative (field selector) (.projection 3) value raw (xs 3) xs
    hr (fieldValue selector raw xs hs) (projectionValue 3 xs)

theorem representativeCheckAccept (representative : Program 2) (selector : Program 1) (endpoint : Fin 4)
    (raw : OTerm α) (xs : Fin 4 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hr : Nonempty (Derivation body Gamma (graph2 representative (xs endpoint) raw (xs 3)))) :
    Nonempty (Derivation body Gamma
      (programGraph (representativeCheck representative selector endpoint) (suc z) xs)) :=
  binaryValue InternalEqualityTest.equalityTest (representativeAt representative selector)
    (.projection endpoint) (suc z) (xs endpoint) (xs endpoint) xs
    (equalityOfEqual (xs endpoint) (xs endpoint) ⟨refl (xs endpoint)⟩)
    (representativeAtValue representative selector raw (xs endpoint) xs hs hr)
    (projectionValue endpoint xs)

/-- The representative value is obtained through original internal Program
totality. Its equality check is inverted by the actual arithmetic proof. -/
theorem representativeCheckRecover (representative : Program 2) (selector : Program 1) (endpoint : Fin 4)
    (raw : OTerm α) (xs : Fin 4 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hc : Nonempty (Derivation body Gamma
      (programGraph (representativeCheck representative selector endpoint) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph2 representative (xs endpoint) raw (xs 3))) := by
  apply programCases representative (Fin.cons raw (Fin.cons (xs 3) Fin.elim0)) (graph2 representative (xs endpoint) raw (xs 3))
  intro β j Delta value hj hv
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hv
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at hc'
  let ys : Fin 4 → OTerm β := fun i => (xs i).relabel j
  have he := binaryRecover InternalEqualityTest.equalityTest
    (representativeAt representative selector) (.projection endpoint) (suc z)
    value ((xs endpoint).relabel j) ys hc'
    (representativeAtValue representative selector (raw.relabel j) value ys hs' hv)
    (projectionValue endpoint ys)
  exact outputTransport representative value ((xs endpoint).relabel j)
    (Fin.cons (raw.relabel j) (Fin.cons ((xs 3).relabel j) Fin.elim0))
    (equalityOfAcceptance value ((xs endpoint).relabel j) he) hv

theorem fieldComponents (xs : Fin 4 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k))) :
    ∀ i : Fin 4, Nonempty (Derivation body Gamma
      (programGraph ((![field source,field target,field step,.projection 3] : Fin 4 → Program 4) i)
        (![s,t,k,xs 3] i) xs)) := by
  obtain ⟨h⟩ := h
  intro i
  exact Fin.cases (fieldValue source s xs ⟨Derivation.conjunctionLeft h⟩)
    (Fin.cases (fieldValue target t xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩)
      (Fin.cases (fieldValue step k xs ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩)
        (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q)))) i

theorem stepAtAccept (data : Data) (oldStep : Program 4) (xs : Fin 4 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k)))
    (hs : Nonempty (Derivation body Gamma (InternalOriginalUniformStepGuard.stepAccepted data oldStep s t k (xs 3)))) :
    Nonempty (Derivation body Gamma (programGraph (stepAt data oldStep) (suc z) xs)) :=
  compositionValue (InternalOriginalUniformStepGuard.stepChecker data oldStep)
    ![field source,field target,field step,.projection 3] (suc z) xs ![s,t,k,xs 3]
    hs (fieldComponents xs s t k h)

theorem stepAtRecover (data : Data) (oldStep : Program 4) (xs : Fin 4 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k)))
    (hs : Nonempty (Derivation body Gamma (programGraph (stepAt data oldStep) (suc z) xs))) :
    Nonempty (Derivation body Gamma (InternalOriginalUniformStepGuard.stepAccepted data oldStep s t k (xs 3))) :=
  compositionRecover (InternalOriginalUniformStepGuard.stepChecker data oldStep)
    ![field source,field target,field step,.projection 3] (suc z) xs ![s,t,k,xs 3]
    hs (fieldComponents xs s t k h)

theorem coreRecover (data : Data) (oldStep : Program 4) (x y certificate s t k parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hc : Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (requirements data oldStep x y s t k parameter)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  obtain ⟨houter⟩ := conjunctionRecover (stepAt data oldStep)
    (InternalAcceptance.conjunction
      (representativeCheck (sourceRepresentative data) source 0)
      (representativeCheck (targetRepresentative data) target 1)) xs hc
  obtain ⟨hinner⟩ := conjunctionRecover
    (representativeCheck (sourceRepresentative data) source 0)
    (representativeCheck (targetRepresentative data) target 1) xs ⟨Derivation.conjunctionRight houter⟩
  obtain ⟨hstep⟩ := stepAtRecover data oldStep xs s t k hf ⟨Derivation.conjunctionLeft houter⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hsource⟩ := representativeCheckRecover (sourceRepresentative data) source 0 s xs
    ⟨Derivation.conjunctionLeft hf⟩ ⟨Derivation.conjunctionLeft hinner⟩
  obtain ⟨htarget⟩ := representativeCheckRecover (targetRepresentative data) target 1 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hf)⟩ ⟨Derivation.conjunctionRight hinner⟩
  exact ⟨Derivation.conjunctionIntroduction hstep (Derivation.conjunctionIntroduction hsource htarget)⟩

theorem coreAccept (data : Data) (oldStep : Program 4) (x y certificate s t k parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hr : Nonempty (Derivation body Gamma (requirements data oldStep x y s t k parameter))) :
    Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter)) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  obtain ⟨hr⟩ := hr
  have hstep := stepAtAccept data oldStep xs s t k hf ⟨Derivation.conjunctionLeft hr⟩
  obtain ⟨hf⟩ := hf
  have hsource := representativeCheckAccept (sourceRepresentative data) source 0 s xs
    ⟨Derivation.conjunctionLeft hf⟩ ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hr)⟩
  have htarget := representativeCheckAccept (targetRepresentative data) target 1 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hf)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hr)⟩
  exact conjunctionAccept (stepAt data oldStep) _ xs hstep
    (conjunctionAccept (representativeCheck (sourceRepresentative data) source 0)
      (representativeCheck (targetRepresentative data) target 1) xs hsource htarget)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSupportProof
