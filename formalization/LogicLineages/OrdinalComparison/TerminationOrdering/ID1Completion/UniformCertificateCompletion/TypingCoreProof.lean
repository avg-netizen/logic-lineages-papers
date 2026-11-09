module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationStepPeelSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open UniformCertificateCompletion.SupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem validityAtRecover (P : Program 2) (i : Fin 4) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (validityAt P i) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph2 P (suc z) (xs i) (xs 3))) :=
  binaryRecover P (.projection i) (.projection 3) (suc z) (xs i) (xs 3) xs
    h (projectionValue i xs) (projectionValue 3 xs)

theorem stepParts (data : Data) (oldStep : Program 4) (s t k parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepAccepted data oldStep s t k parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) s parameter)) ∧
      Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) t parameter)) ∧
      Nonempty (Derivation body Gamma (programGraph sameOuterTypes (suc z) ![s,t,k,parameter])) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  have ho := conjunctionRecover _ _ xs h
  have hb := conjunctionRecover _ _ xs (andLeft ho)
  have hg := conjunctionRecover _ _ xs (andLeft hb)
  have hi := conjunctionRecover _ _ xs (andRight hg)
  exact ⟨validityAtRecover (validity data) 0 xs (andLeft hg),
    validityAtRecover (validity data) 1 xs (andRight ho), andRight hi⟩

theorem sourceFold (data : Data) (x s parameter : OTerm α)
    (hv : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) s parameter)))
    (hn : Nonempty (Derivation body Gamma (graph2 (sourceRepresentative data) x s parameter))) :
    Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.foldGraph data x s parameter)) := by
  let xs : Fin 2 → OTerm α := ![s,parameter]
  exact successorBranchElim (InternalApplicationValidityStack.exactOne (validity data))
    (InternalAcceptance.constantZero 2) (InternalParameterizedCanonicalResultFold.foldN data)
    x z xs
    (sameAccept (validity data) (InternalLessThan.constantOne 2) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hn

/-- Recover the right graph from an accepted original equality test and its
known left graph. The unknown right value is obtained by internal totality. -/
theorem sameLeftRecover {n : Nat} (p q : Program n) (value : OTerm α) (xs : Fin n → OTerm α)
    (he : Nonempty (Derivation body Gamma (programGraph (InternalApplicationStepPeel.same p q) (suc z) xs)))
    (hp : Nonempty (Derivation body Gamma (programGraph p value xs))) :
    Nonempty (Derivation body Gamma (programGraph q value xs)) := by
  apply programCases q xs _
  intro β j Delta right hj hr
  simp only [programRename]
  have he' := renameInto he j Delta hj
  have hp' := renameInto hp j Delta hj
  simp only [programRename,sucRelabel,zRelabel] at he' hp'
  obtain ⟨hEq⟩ := InternalEqualityTestProof.equalityOfAcceptance (value.relabel j) right
    (binaryRecover InternalEqualityTest.equalityTest p q (suc z) (value.relabel j) right
      (fun i => (xs i).relabel j) he' hp' hr)
  exact outputTransport q right (value.relabel j) (fun i => (xs i).relabel j) ⟨symm hEq⟩ hr

theorem targetTag (s t k typ parameter : OTerm α)
    (he : Nonempty (Derivation body Gamma (programGraph sameOuterTypes (suc z) ![s,t,k,parameter])))
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ s))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ t)) := by
  let xs : Fin 4 → OTerm α := ![s,t,k,parameter]
  have ht := sameLeftRecover (leftOf (.projection 0)) (leftOf (.projection 1)) typ xs he
    (unaryValue InternalUnpair.left (.projection 0) typ s xs hs (projectionValue 0 xs))
  exact unaryRecover InternalUnpair.left (.projection 1) typ t xs ht (projectionValue 1 xs)

theorem rawWithTag (data : Data) (oldStep : Program 4)
    (x y s t k typ tag parameter : OTerm α)
    (ht : Nonempty (Derivation body Gamma (typedAccepted data x typ parameter)))
    (he : Nonempty (Derivation body Gamma (requirements data oldStep x y s t k parameter)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag s))) :
    Nonempty (Derivation body Gamma (typedAccepted data y typ parameter)) := by
  obtain ⟨hs,hv,htags⟩ := stepParts data oldStep s t k parameter (andLeft he)
  have hn := sourceFold data x s parameter hs (andLeft (andRight he))
  obtain ⟨hc⟩ := InternalParameterizedCanonicalResultFoldProof.actualParameterizedCanonicalFoldOutputInvariant
    body data α Gamma x s tag parameter
  obtain ⟨hp⟩ := andIntro hs hl
  obtain ⟨hn'⟩ := hn
  have ho := (⟨Derivation.implicationElimination (Derivation.implicationElimination hc hp) hn'⟩ :
    Nonempty (Derivation body Gamma (InternalParameterizedCanonicalResultFold.successfulOutput data x s tag parameter)))
  have hf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member x typ parameter ht
  have heq := valueUnique InternalUnpair.left tag typ ![x]
    (andLeft (andRight (andRight ho))) (andLeft (andRight (andRight hf)))
  have hsource := outputTransport InternalUnpair.left tag typ ![s] heq hl
  have htarget := targetTag s t k typ parameter htags hsource
  obtain ⟨hconsumer⟩ := InternalParameterizedCanonicalResultFoldProof.actualParameterizedCanonicalFoldTypedOutput
    body data α Gamma y t typ parameter
  obtain ⟨hinput⟩ := andIntro hv htarget
  obtain ⟨hmember⟩ := andLeft hf
  obtain ⟨houtput⟩ := andRight (andRight he)
  exact andRight ⟨Derivation.implicationElimination
    (Derivation.implicationElimination (Derivation.implicationElimination hconsumer hinput) hmember) houtput⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof
