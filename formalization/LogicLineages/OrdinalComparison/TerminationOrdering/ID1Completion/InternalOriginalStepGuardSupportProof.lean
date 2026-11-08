module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalStepGuard InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalEqualityTestProof InternalEqualityTestCompositionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

 theorem atValue (p : Program 1) (i : Fin 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 p out (xs i)))) :
    Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs)) :=
  unaryValue p (.projection i) out (xs i) xs h (projectionValue i xs)

 theorem atRecover (p : Program 1) (i : Fin 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs))) :
    Nonempty (Derivation body Gamma (graph1 p out (xs i))) :=
  unaryRecover p (.projection i) out (xs i) xs h (projectionValue i xs)

 theorem checkerRecover (data : Data) (oldChecker : Program 3)
    (sourceTag targetTag s t k : OTerm α)
    (htag : Nonempty (Derivation body Gamma (tagGraphs sourceTag targetTag s t)))
    (hc : Nonempty (Derivation body Gamma (accepted data oldChecker s t k))) :
    Nonempty (Derivation body Gamma (requirements data oldChecker sourceTag targetTag s t k)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  obtain ⟨hout⟩ := conjunctionRecover (guards data) oldChecker xs hc
  obtain ⟨hguards⟩ := conjunctionRecover (sourceAt data)
    (InternalAcceptance.conjunction (targetAt data) sameOuterTypes) xs
      ⟨Derivation.conjunctionLeft hout⟩
  obtain ⟨hinner⟩ := conjunctionRecover (targetAt data) sameOuterTypes xs
    ⟨Derivation.conjunctionRight hguards⟩
  obtain ⟨hsource⟩ := atRecover data.sourceValid 0 one xs ⟨Derivation.conjunctionLeft hguards⟩
  obtain ⟨htarget⟩ := atRecover data.targetValid 1 one xs ⟨Derivation.conjunctionLeft hinner⟩
  obtain ⟨htag⟩ := htag
  have he := binaryRecover InternalEqualityTest.equalityTest
    (leftOf (.projection 0)) (leftOf (.projection 1)) one sourceTag targetTag xs
    ⟨Derivation.conjunctionRight hinner⟩
    (atValue InternalUnpair.left 0 sourceTag xs ⟨Derivation.conjunctionLeft htag⟩)
    (atValue InternalUnpair.left 1 targetTag xs ⟨Derivation.conjunctionRight htag⟩)
  obtain ⟨he⟩ := equalityOfAcceptance sourceTag targetTag he
  simp only [requirements,equalEqn]
  exact ⟨Derivation.conjunctionIntroduction hsource (Derivation.conjunctionIntroduction htarget
    (Derivation.conjunctionIntroduction he (Derivation.conjunctionRight hout)))⟩

 theorem checkerAccept (data : Data) (oldChecker : Program 3)
    (sourceTag targetTag s t k : OTerm α)
    (htag : Nonempty (Derivation body Gamma (tagGraphs sourceTag targetTag s t)))
    (hr : Nonempty (Derivation body Gamma (requirements data oldChecker sourceTag targetTag s t k))) :
    Nonempty (Derivation body Gamma (accepted data oldChecker s t k)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  obtain ⟨hr⟩ := hr
  obtain ⟨htag⟩ := htag
  have hsource := atValue data.sourceValid 0 one xs ⟨Derivation.conjunctionLeft hr⟩
  have htarget := atValue data.targetValid 1 one xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hr)⟩
  have he := binaryValue InternalEqualityTest.equalityTest
    (leftOf (.projection 0)) (leftOf (.projection 1)) one sourceTag targetTag xs
    (equalityOfEqual sourceTag targetTag
      ⟨by simpa only [equalEqn] using Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hr))⟩)
    (atValue InternalUnpair.left 0 sourceTag xs ⟨Derivation.conjunctionLeft htag⟩)
    (atValue InternalUnpair.left 1 targetTag xs ⟨Derivation.conjunctionRight htag⟩)
  exact conjunctionAccept (guards data) oldChecker xs
    (conjunctionAccept (sourceAt data) _ xs hsource
      (conjunctionAccept (targetAt data) sameOuterTypes xs htarget he))
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hr))⟩

 theorem oneRename {β : Type} (j : α → β) :
    (one : OTerm α).relabel j = one := by
  change (suc z).relabel j = suc z
  rw [sucRelabel,zRelabel]

 theorem acceptedRename {β : Type} (data : Data) (oldChecker : Program 3)
    (s t k : OTerm α) (j : α → β) :
    (accepted data oldChecker s t k).relabel j =
      accepted data oldChecker (s.relabel j) (t.relabel j) (k.relabel j) := by
  unfold accepted
  rw [graph3Rename,oneRename]

 theorem taggedRequirementsRename {β : Type} (data : Data) (oldChecker : Program 3)
    (tag s t k : OTerm α) (j : α → β) :
    (taggedRequirements data oldChecker tag s t k).relabel j =
      taggedRequirements data oldChecker (tag.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) := by
  change (graph1 data.sourceValid one s).relabel j ⊓
    ((graph1 data.targetValid one t).relabel j ⊓
      ((graph1 InternalUnpair.left tag t).relabel j ⊓ (graph3 oldChecker one s t k).relabel j)) = _
  rw [graph1Rename,graph1Rename,graph1Rename,graph3Rename,oneRename]
  rfl

 theorem taggedRecover (data : Data) (oldChecker : Program 3) (tag s t k : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s)))
    (hc : Nonempty (Derivation body Gamma (accepted data oldChecker s t k))) :
    Nonempty (Derivation body Gamma (taggedRequirements data oldChecker tag s t k)) := by
  apply programCases InternalUnpair.left (Fin.cons t Fin.elim0)
    (taggedRequirements data oldChecker tag s t k)
  intro β j Delta value hj hv
  rw [taggedRequirementsRename]
  simp only [consTermRename,emptyRename] at hv
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  have hc' := renameInto hc j Delta hj
  rw [acceptedRename] at hc'
  obtain ⟨hs'⟩ := hs'
  obtain ⟨hv'⟩ := hv
  obtain ⟨hr⟩ := checkerRecover data oldChecker (tag.relabel j) value
    (s.relabel j) (t.relabel j) (k.relabel j)
    ⟨Derivation.conjunctionIntroduction hs' hv'⟩ hc'
  have he := Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hr))
  simp only [equalEqn] at he
  obtain ⟨ht⟩ := outputTransport InternalUnpair.left value (tag.relabel j)
    (Fin.cons (t.relabel j) Fin.elim0) ⟨symm he⟩ ⟨hv'⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hr)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionRight hr))
      (Derivation.conjunctionIntroduction ht
        (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hr)))))⟩

 theorem taggedAccept (data : Data) (oldChecker : Program 3) (tag s t k : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s)))
    (hr : Nonempty (Derivation body Gamma (taggedRequirements data oldChecker tag s t k))) :
    Nonempty (Derivation body Gamma (accepted data oldChecker s t k)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨hr⟩ := hr
  apply checkerAccept data oldChecker tag tag s t k
  · exact ⟨Derivation.conjunctionIntroduction hs
      (Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight hr)))⟩
  · simp only [requirements,equalEqn]
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft hr)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionRight hr))
        (Derivation.conjunctionIntroduction (refl tag)
          (Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight hr)))))⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardSupportProof
