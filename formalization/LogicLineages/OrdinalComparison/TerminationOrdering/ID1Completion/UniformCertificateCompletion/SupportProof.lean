module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem edgeRename {β : Type} (data : InternalOriginalUniformDescentSelection.Data)
    (oldStep : Program 4) (x y certificate parameter : OTerm α) (j : α → β) :
    (edgeAccepted data oldStep x y certificate parameter).relabel j =
      edgeAccepted data oldStep (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j) := by
  simp only [edgeAccepted, graph4Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel]

theorem typedRename {β : Type} (data : InternalOriginalUniformDescentSelection.Data)
    (x typ parameter : OTerm α) (j : α → β) :
    (typedAccepted data x typ parameter).relabel j =
      typedAccepted data (x.relabel j) (typ.relabel j) (parameter.relabel j) := by
  simp only [typedAccepted, InternalOriginalUniformDescentSelection.typedAccepted,
    graph3Rename, InternalOriginalStepGuard.one, sucRelabel, zRelabel]

theorem requirementsRename {β : Type} (data : InternalOriginalUniformDescentSelection.Data)
    (oldStep : Program 4) (x y s t k parameter : OTerm α) (j : α → β) :
    (requirements data oldStep x y s t k parameter).relabel j =
      requirements data oldStep (x.relabel j) (y.relabel j) (s.relabel j)
        (t.relabel j) (k.relabel j) (parameter.relabel j) := by
  simp only [requirements, stepAccepted, graph4Rename, graph2Rename, conjunctionRename,
    InternalOriginalStepGuard.one, sucRelabel, zRelabel]

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

theorem representativeCheckAccept (representative : Program 2) (selector : Program 1)
    (endpoint : Fin 4) (raw : OTerm α) (xs : Fin 4 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hr : Nonempty (Derivation body Gamma (graph2 representative (xs endpoint) raw (xs 3)))) :
    Nonempty (Derivation body Gamma
      (programGraph (representativeCheck representative selector endpoint) (suc z) xs)) :=
  sameAccept (representativeAt representative selector) (.projection endpoint) (xs endpoint) xs
    (representativeAtValue representative selector raw (xs endpoint) xs hs hr)
    (projectionValue endpoint xs)

theorem representativeCheckRecover (representative : Program 2) (selector : Program 1)
    (endpoint : Fin 4) (raw : OTerm α) (xs : Fin 4 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector raw (xs 2))))
    (hc : Nonempty (Derivation body Gamma
      (programGraph (representativeCheck representative selector endpoint) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph2 representative (xs endpoint) raw (xs 3))) := by
  have hr := sameRightRecover (representativeAt representative selector) (.projection endpoint)
    (xs endpoint) xs hc (projectionValue endpoint xs)
  exact binaryRecover representative (field selector) (.projection 3) (xs endpoint) raw (xs 3) xs
    hr (fieldValue selector raw xs hs) (projectionValue 3 xs)

theorem fieldComponents (xs : Fin 4 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k))) :
    ∀ i : Fin 4, Nonempty (Derivation body Gamma
      (programGraph ((![field source,field target,field step,.projection 3] : Fin 4 → Program 4) i)
        ((![s,t,k,xs 3] : Fin 4 → OTerm α) i) xs)) := by
  intro i
  exact Fin.cases (fieldValue source s xs (andLeft h))
    (Fin.cases (fieldValue target t xs (andLeft (andRight h)))
      (Fin.cases (fieldValue step k xs (andRight (andRight h)))
        (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q)))) i

theorem stepAtAccept (data : InternalOriginalUniformDescentSelection.Data) (oldStep : Program 4)
    (xs : Fin 4 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k)))
    (hs : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k (xs 3)))) :
    Nonempty (Derivation body Gamma (programGraph (stepAt data oldStep) (suc z) xs)) :=
  compositionValue (stepChecker data oldStep) ![field source,field target,field step,.projection 3]
    (suc z) xs ![s,t,k,xs 3] hs (fieldComponents xs s t k h)

theorem stepAtRecover (data : InternalOriginalUniformDescentSelection.Data) (oldStep : Program 4)
    (xs : Fin 4 → OTerm α) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (selectors (xs 2) s t k)))
    (hs : Nonempty (Derivation body Gamma (programGraph (stepAt data oldStep) (suc z) xs))) :
    Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k (xs 3))) :=
  compositionRecover (stepChecker data oldStep) ![field source,field target,field step,.projection 3]
    (suc z) xs ![s,t,k,xs 3] hs (fieldComponents xs s t k h)

theorem checkerRecover (data : InternalOriginalUniformDescentSelection.Data) (oldStep : Program 4)
    (x y certificate s t k parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hc : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (requirements data oldStep x y s t k parameter)) := by
  let xs : Fin 4 → OTerm α := ![x,y,certificate,parameter]
  have ho := conjunctionRecover (stepAt data oldStep)
    (InternalAcceptance.conjunction
      (representativeCheck (sourceRepresentative data) source 0)
      (representativeCheck (targetRepresentative data) target 1)) xs hc
  have hi := conjunctionRecover
    (representativeCheck (sourceRepresentative data) source 0)
    (representativeCheck (targetRepresentative data) target 1) xs (andRight ho)
  exact andIntro (stepAtRecover data oldStep xs s t k hf (andLeft ho))
    (andIntro (representativeCheckRecover (sourceRepresentative data) source 0 s xs
      (andLeft hf) (andLeft hi))
      (representativeCheckRecover (targetRepresentative data) target 1 t xs
        (andLeft (andRight hf)) (andRight hi)))

theorem checkerAccept (data : InternalOriginalUniformDescentSelection.Data) (oldStep : Program 4)
    (x y certificate s t k parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hr : Nonempty (Derivation body Gamma (requirements data oldStep x y s t k parameter))) :
    Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y certificate parameter)) := by
  let xs : Fin 4 → OTerm α := ![x,y,certificate,parameter]
  exact conjunctionAccept (stepAt data oldStep) _ xs
    (stepAtAccept data oldStep xs s t k hf (andLeft hr))
    (conjunctionAccept
      (representativeCheck (sourceRepresentative data) source 0)
      (representativeCheck (targetRepresentative data) target 1) xs
      (representativeCheckAccept (sourceRepresentative data) source 0 s xs
        (andLeft hf) (andLeft (andRight hr)))
      (representativeCheckAccept (targetRepresentative data) target 1 t xs
        (andLeft (andRight hf)) (andRight (andRight hr))))

theorem actualParameterizedQuotientEdgeFactorization :
    Targets.ActualParameterizedQuotientEdgeFactorization := by
  intro data oldStep body α Delta x y certificate s t k parameter
  let P := selectors certificate s t k
  let E := edgeAccepted data oldStep x y certificate parameter
  let Q := requirements data oldStep x y s t k parameter
  have hf : Nonempty (Derivation body (E :: P :: Delta) P) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have he : Nonempty (Derivation body (E :: P :: Delta) E) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := checkerRecover data oldStep x y certificate s t k parameter hf he
  have hb : Nonempty (Derivation body (Q :: P :: Delta) P) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hq : Nonempty (Derivation body (Q :: P :: Delta) Q) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := checkerAccept data oldStep x y certificate s t k parameter hb hq
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.SupportProof
