module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalQuotientEdgeChecker InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem fieldValue (selector : Program 1) (value : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 selector value (xs 2)))) :
    Nonempty (Derivation body Gamma (programGraph (field selector) value xs)) :=
  unaryValue selector (.projection 2) value (xs 2) xs h (projectionValue 2 xs)

theorem representativeAtValue (representative selector : Program 1)
    (raw value : OTerm α) (xs : Fin 3 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hr : Nonempty (Derivation body Gamma (graph1 representative value raw))) :
    Nonempty (Derivation body Gamma (programGraph (representativeAt representative selector) value xs)) :=
  unaryValue representative (field selector) value raw xs hr (fieldValue selector raw xs hs)

theorem representativeCheckAccept (representative selector : Program 1) (endpoint : Fin 3)
    (raw : OTerm α) (xs : Fin 3 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hr : Nonempty (Derivation body Gamma (graph1 representative (xs endpoint) raw))) :
    Nonempty (Derivation body Gamma
      (programGraph (representativeCheck representative selector endpoint) (suc z) xs)) :=
  binaryValue InternalEqualityTest.equalityTest (representativeAt representative selector)
    (.projection endpoint) (suc z) (xs endpoint) (xs endpoint) xs
    (equalityOfEqual (xs endpoint) (xs endpoint) ⟨refl (xs endpoint)⟩)
    (representativeAtValue representative selector raw (xs endpoint) xs hs hr)
    (projectionValue endpoint xs)

/-- The representative value is obtained through original internal Program
totality. Its equality check is inverted by the actual arithmetic proof. -/
theorem representativeCheckRecover (representative selector : Program 1) (endpoint : Fin 3)
    (raw : OTerm α) (xs : Fin 3 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hc : Nonempty (Derivation body Gamma
      (programGraph (representativeCheck representative selector endpoint) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph1 representative (xs endpoint) raw)) := by
  apply programCases representative (Fin.cons raw Fin.elim0) (graph1 representative (xs endpoint) raw)
  intro β j Delta value hj hv
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hv
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at hc'
  let ys : Fin 3 → OTerm β := fun i => (xs i).relabel j
  have he := binaryRecover InternalEqualityTest.equalityTest
    (representativeAt representative selector) (.projection endpoint) (suc z)
    value ((xs endpoint).relabel j) ys hc'
    (representativeAtValue representative selector (raw.relabel j) value ys hs' hv)
    (projectionValue endpoint ys)
  exact outputTransport representative value ((xs endpoint).relabel j)
    (Fin.cons (raw.relabel j) Fin.elim0)
    (equalityOfAcceptance value ((xs endpoint).relabel j) he) hv

theorem fieldComponents (xs : Fin 3 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k))) :
    ∀ i : Fin 3, Nonempty (Derivation body Gamma
      (programGraph ((![field source,field target,field step] : Fin 3 → Program 3) i)
        (![s,t,k] i) xs)) := by
  obtain ⟨h⟩ := h
  intro i
  exact Fin.cases (fieldValue source s xs ⟨Derivation.conjunctionLeft h⟩)
    (Fin.cases (fieldValue target t xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩)
      (Fin.cases (fieldValue step k xs ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩)
        (fun q => Fin.elim0 q))) i

theorem stepAtAccept (data : Data) (xs : Fin 3 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k)))
    (hs : Nonempty (Derivation body Gamma (graph3 data.stepProgram (suc z) s t k))) :
    Nonempty (Derivation body Gamma (programGraph (stepAt data) (suc z) xs)) :=
  compositionValue data.stepProgram ![field source,field target,field step] (suc z) xs ![s,t,k]
    hs (fieldComponents xs s t k h)

theorem stepAtRecover (data : Data) (xs : Fin 3 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k)))
    (hs : Nonempty (Derivation body Gamma (programGraph (stepAt data) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph3 data.stepProgram (suc z) s t k)) :=
  compositionRecover data.stepProgram ![field source,field target,field step] (suc z) xs ![s,t,k]
    hs (fieldComponents xs s t k h)

theorem checkerRecover (data : Data) (x y certificate s t k : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hc : Nonempty (Derivation body Gamma (accepted data x y certificate))) :
    Nonempty (Derivation body Gamma (requirements data x y s t k)) := by
  let xs : Fin 3 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate Fin.elim0))
  obtain ⟨houter⟩ := conjunctionRecover (stepAt data)
    (InternalAcceptance.conjunction
      (representativeCheck data.sourceRepresentative source 0)
      (representativeCheck data.targetRepresentative target 1)) xs hc
  obtain ⟨hinner⟩ := conjunctionRecover
    (representativeCheck data.sourceRepresentative source 0)
    (representativeCheck data.targetRepresentative target 1) xs ⟨Derivation.conjunctionRight houter⟩
  obtain ⟨hstep⟩ := stepAtRecover data xs s t k hf ⟨Derivation.conjunctionLeft houter⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hsource⟩ := representativeCheckRecover data.sourceRepresentative source 0 s xs
    ⟨Derivation.conjunctionLeft hf⟩ ⟨Derivation.conjunctionLeft hinner⟩
  obtain ⟨htarget⟩ := representativeCheckRecover data.targetRepresentative target 1 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hf)⟩ ⟨Derivation.conjunctionRight hinner⟩
  exact ⟨Derivation.conjunctionIntroduction hstep (Derivation.conjunctionIntroduction hsource htarget)⟩

theorem checkerAccept (data : Data) (x y certificate s t k : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hr : Nonempty (Derivation body Gamma (requirements data x y s t k))) :
    Nonempty (Derivation body Gamma (accepted data x y certificate)) := by
  let xs : Fin 3 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate Fin.elim0))
  obtain ⟨hr⟩ := hr
  have hstep := stepAtAccept data xs s t k hf ⟨Derivation.conjunctionLeft hr⟩
  obtain ⟨hf⟩ := hf
  have hsource := representativeCheckAccept data.sourceRepresentative source 0 s xs
    ⟨Derivation.conjunctionLeft hf⟩ ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hr)⟩
  have htarget := representativeCheckAccept data.targetRepresentative target 1 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hf)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hr)⟩
  exact conjunctionAccept (stepAt data) _ xs hstep
    (conjunctionAccept (representativeCheck data.sourceRepresentative source 0)
      (representativeCheck data.targetRepresentative target 1) xs hsource htarget)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerSupportProof
