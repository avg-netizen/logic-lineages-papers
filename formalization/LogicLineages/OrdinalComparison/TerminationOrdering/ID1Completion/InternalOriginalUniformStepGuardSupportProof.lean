module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformStepGuard InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalStepGuard (one)
open InternalOriginalStepGuardSupportProof (oneRename)
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atValue (P : Program 2) (i : Fin 4) (out : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 P out (xs i) (xs 3)))) :
    Nonempty (Derivation body Gamma (programGraph (atParameter P i) out xs)) :=
  binaryValue P (.projection i) (.projection 3) out (xs i) (xs 3) xs h
    (projectionValue i xs) (projectionValue 3 xs)

theorem atRecover (P : Program 2) (i : Fin 4) (out : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (atParameter P i) out xs))) :
    Nonempty (Derivation body Gamma (graph2 P out (xs i) (xs 3))) :=
  binaryRecover P (.projection i) (.projection 3) out (xs i) (xs 3) xs h
    (projectionValue i xs) (projectionValue 3 xs)

theorem leftAtValue (i : Fin 4) (out : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left out (xs i)))) :
    Nonempty (Derivation body Gamma (programGraph (leftOf (.projection i)) out xs)) :=
  unaryValue InternalUnpair.left (.projection i) out (xs i) xs h (projectionValue i xs)

/-- Expose the actual guards before any outer-type witness is chosen. -/
theorem guardedParts (sourceValid targetValid : Program 2) (core : Program 4)
    (s t k parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (guardedAccepted sourceValid targetValid core s t k parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 sourceValid one s parameter ⊓
        (graph2 targetValid one t parameter ⊓
          (graph4 sameOuterTypes one s t k parameter ⊓ graph4 core one s t k parameter)))) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  have hout := conjunctionRecover (guards sourceValid targetValid) core xs h
  have hg := conjunctionRecover (atParameter sourceValid 0)
    (InternalAcceptance.conjunction (atParameter targetValid 1) sameOuterTypes) xs (andLeft hout)
  have hi := conjunctionRecover (atParameter targetValid 1) sameOuterTypes xs (andRight hg)
  exact andIntro (atRecover sourceValid 0 one xs (andLeft hg))
    (andIntro (atRecover targetValid 1 one xs (andLeft hi))
      (andIntro (andRight hi) (andRight hout)))

theorem guardedAcceptedRename {β : Type} (sourceValid targetValid : Program 2)
    (core : Program 4) (s t k parameter : OTerm α) (j : α → β) :
    (guardedAccepted sourceValid targetValid core s t k parameter).relabel j =
      guardedAccepted sourceValid targetValid core
        (s.relabel j) (t.relabel j) (k.relabel j) (parameter.relabel j) := by
  unfold guardedAccepted
  rw [graph4Rename,oneRename]

theorem taggedRequirementsRename {β : Type} (sourceValid targetValid : Program 2)
    (core : Program 4) (tag s t k parameter : OTerm α) (j : α → β) :
    (taggedRequirements sourceValid targetValid core tag s t k parameter).relabel j =
      taggedRequirements sourceValid targetValid core (tag.relabel j)
        (s.relabel j) (t.relabel j) (k.relabel j) (parameter.relabel j) := by
  change (graph2 sourceValid one s parameter).relabel j ⊓
    ((graph2 targetValid one t parameter).relabel j ⊓
      ((graph1 InternalUnpair.left tag t).relabel j ⊓
        (graph4 core one s t k parameter).relabel j)) = _
  rw [graph2Rename,graph2Rename,graph1Rename,graph4Rename,oneRename]
  rfl

/-- Original totality supplies the target tag. The accepted original
equality test then identifies it with the independently supplied source tag. -/
theorem taggedRecover (sourceValid targetValid : Program 2) (core : Program 4)
    (tag s t k parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s)))
    (hc : Nonempty (Derivation body Gamma
      (guardedAccepted sourceValid targetValid core s t k parameter))) :
    Nonempty (Derivation body Gamma
      (taggedRequirements sourceValid targetValid core tag s t k parameter)) := by
  apply programCases InternalUnpair.left (Fin.cons t Fin.elim0)
    (taggedRequirements sourceValid targetValid core tag s t k parameter)
  intro β j Delta value hj hv
  rw [taggedRequirementsRename]
  simp only [consTermRename,emptyRename] at hv
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hc' := renameInto hc j Delta hj
  rw [guardedAcceptedRename] at hc'
  have hr := guardedParts sourceValid targetValid core
    (s.relabel j) (t.relabel j) (k.relabel j) (parameter.relabel j) hc'
  let xs : Fin 4 → OTerm β := ![s.relabel j,t.relabel j,k.relabel j,parameter.relabel j]
  have he := binaryRecover InternalEqualityTest.equalityTest
    (leftOf (.projection 0)) (leftOf (.projection 1)) one (tag.relabel j) value xs
    (andLeft (andRight (andRight hr)))
    (leftAtValue 0 (tag.relabel j) xs hs') (leftAtValue 1 value xs hv)
  obtain ⟨he⟩ := equalityOfAcceptance (tag.relabel j) value he
  obtain ⟨ht⟩ := outputTransport InternalUnpair.left value (tag.relabel j)
    (Fin.cons (t.relabel j) Fin.elim0) ⟨symm he⟩ hv
  exact andIntro (andLeft hr)
    (andIntro (andLeft (andRight hr))
      (andIntro ⟨ht⟩ (andRight (andRight (andRight hr)))))

theorem taggedAccept (sourceValid targetValid : Program 2) (core : Program 4)
    (tag s t k parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s)))
    (hr : Nonempty (Derivation body Gamma
      (taggedRequirements sourceValid targetValid core tag s t k parameter))) :
    Nonempty (Derivation body Gamma
      (guardedAccepted sourceValid targetValid core s t k parameter)) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  have ht := andLeft (andRight (andRight hr))
  have he := binaryValue InternalEqualityTest.equalityTest
    (leftOf (.projection 0)) (leftOf (.projection 1)) one tag tag xs
    (equalityOfEqual tag tag ⟨refl tag⟩)
    (leftAtValue 0 tag xs hs) (leftAtValue 1 tag xs ht)
  exact conjunctionAccept (guards sourceValid targetValid) core xs
    (conjunctionAccept (atParameter sourceValid 0) _ xs
      (atValue sourceValid 0 one xs (andLeft hr))
      (conjunctionAccept (atParameter targetValid 1) sameOuterTypes xs
        (atValue targetValid 1 one xs (andLeft (andRight hr))) he))
    (andRight (andRight (andRight hr)))

/-- The two literal W conjuncts, with the binary parameter wiring removed. -/
theorem stepRecover (data : Data) (oldStep : Program 4) (s t k parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Gamma
      (guardedAccepted (validity data) (targetValidity data)
          (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) s t k parameter ⊓
        graph2 (validity data) one t parameter)) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  have hr := conjunctionRecover (guardedStep data oldStep) (targetSourceValidityAt data) xs h
  exact andIntro (andLeft hr) (atRecover (validity data) 1 one xs (andRight hr))

theorem stepAccept (data : Data) (oldStep : Program 4) (s t k parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (guardedAccepted (validity data) (targetValidity data)
        (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) s t k parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 (validity data) one t parameter))) :
    Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter)) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  exact conjunctionAccept (guardedStep data oldStep) (targetSourceValidityAt data) xs hs
    (atValue (validity data) 1 one xs ht)

theorem stepSourceValidity (data : Data) (oldStep : Program 4) (s t k parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validity data) one s parameter)) :=
  andLeft (guardedParts (validity data) (targetValidity data)
    (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep) s t k parameter
    (andLeft (stepRecover data oldStep s t k parameter h)))

theorem stepTargetSourceValidity (data : Data) (oldStep : Program 4) (s t k parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validity data) one t parameter)) :=
  andRight (stepRecover data oldStep s t k parameter h)

theorem taggedStepRecover (data : Data) (oldStep : Program 4)
    (tag s t k parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s)))
    (h : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Gamma (stepRequirements data oldStep tag s t k parameter)) := by
  have hw := stepRecover data oldStep s t k parameter h
  have hr := taggedRecover (validity data) (targetValidity data)
    (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)
    tag s t k parameter hs (andLeft hw)
  exact andIntro (andLeft hr) (andIntro (andRight hw) (andRight hr))

theorem taggedStepAccept (data : Data) (oldStep : Program 4)
    (tag s t k parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s)))
    (h : Nonempty (Derivation body Gamma (stepRequirements data oldStep tag s t k parameter))) :
    Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter)) := by
  apply stepAccept data oldStep s t k parameter
  · exact taggedAccept (validity data) (targetValidity data)
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)
      tag s t k parameter hs (andIntro (andLeft h) (andRight (andRight h)))
  · exact andLeft (andRight h)

theorem actualParameterizedGuardedStepAtSourceTag :
    InternalOriginalUniformStepGuardTargets.ActualParameterizedGuardedStepAtSourceTag := by
  intro body sourceValid targetValid core α Delta tag s t k parameter
  let A := graph1 InternalUnpair.left tag s
  let P := guardedAccepted sourceValid targetValid core s t k parameter
  let Q := taggedRequirements sourceValid targetValid core tag s t k parameter
  obtain ⟨hf⟩ := taggedRecover (body := body) (Gamma := P :: A :: Delta)
    sourceValid targetValid core tag s t k parameter
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := taggedAccept (body := body) (Gamma := Q :: A :: Delta)
    sourceValid targetValid core tag s t k parameter
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualParameterizedCanonicalStepAtSourceTag :
    InternalOriginalUniformStepGuardTargets.ActualParameterizedCanonicalStepAtSourceTag := by
  intro body data oldStep α Delta tag s t k parameter
  let A := graph1 InternalUnpair.left tag s
  let P := stepAccepted data oldStep s t k parameter
  let Q := stepRequirements data oldStep tag s t k parameter
  obtain ⟨hf⟩ := taggedStepRecover (body := body) (Gamma := P :: A :: Delta)
    data oldStep tag s t k parameter
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := taggedStepAccept (body := body) (Gamma := Q :: A :: Delta)
    data oldStep tag s t k parameter
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
