module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalBetaTotalityProof (addHyp)
open InternalParameterizedApplicationValidityFold
open InternalParameterizedApplicationResultStack (liftP)
open SourceComputabilityCompletion.BottomRepresentative (constant bottomCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem constantValue {n : Nat} (k : Nat) (xs : Fin n → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph (constant k) (numeral k) xs)) := by
  induction k with
  | zero => exact constantZeroValue xs
  | succ k ih =>
    exact unaryValue .succ (constant k) (numeral (k+1)) (numeral k) xs
      (successorValue (Fin.cons (numeral k) Fin.elim0)) ih

theorem bottomConstructorTag (input typ : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (graph1 bottomCode input typ))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationStepPeel.constructorTag (.projection 0)) (numeral 3) input)) := by
  let pay : Program 1 := BottomSourceShapeProof.bottomPayload
  apply programCases pay (Fin.cons typ Fin.elim0) _
  intro β j Delta payload hj hv
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have h' := renameInto h j Delta hj
  rw [graph1Rename] at h'
  rw [BottomSourceShapeProof.bottomCodeProgram] at h'
  have hv' : Nonempty (Derivation body Delta (graph1 pay payload (typ.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hv
  let xs : Fin 1 → OrdinaryArithmetic.Term β := (Fin.cons (typ.relabel j) Fin.elim0)
  let ys : Fin 1 → OrdinaryArithmetic.Term β := (Fin.cons (input.relabel j) Fin.elim0)
  have hpay := binaryRecover InternalPairing.pairing (constant 3) (.projection 0)
    payload (numeral 3) (typ.relabel j) xs hv' (constantValue 3 xs) (projectionValue 0 xs)
  have hout := compositionRecover InternalPairing.pairing (Fin.cons (.projection (0 : Fin 1)) (Fin.cons pay Fin.elim0))
    (input.relabel j) xs (Fin.cons (typ.relabel j) (Fin.cons payload Fin.elim0)) h'
    (fun i => Fin.cases (projectionValue 0 xs) (Fin.cases hv' (fun k => Fin.elim0 k)) i)
  have hr := unaryValue InternalUnpair.right (.projection (0 : Fin 1)) payload (input.relabel j)
    ys (pairRight (input.relabel j) (typ.relabel j) payload hout) (projectionValue 0 ys)
  exact unaryValue InternalUnpair.left (rightOf (.projection (0 : Fin 1)))
    (numeral 3) payload ys (pairLeft payload (numeral 3) (typ.relabel j) hpay) hr

theorem bottomOpeningZero (guard : Program 2) (input typ parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (graph1 bottomCode input typ))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) z input parameter)) := by
  let tag : Program 1 := InternalApplicationStepPeel.constructorTag (.projection 0)
  let test : Program 1 := InternalApplicationStepPeel.same tag (two 1)
  let xs : Fin 2 → OrdinaryArithmetic.Term α := (Fin.cons input (Fin.cons parameter Fin.elim0))
  let P := graph2 (InternalParameterizedApplicationResultStack.openGuardP guard) (suc z) input parameter
  have htag := bottomConstructorTag input typ h
  have hn : Nonempty (Derivation body Gamma P.not) := by
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := conjunctionRecover (liftP test) guard xs hp
    have ht := InternalParameterizedApplicationResultStackWiringProof.liftRecover test (suc z) input parameter
      (andLeft hf)
    have ht2 := sameRightRecover tag (two 1) positionTerm (Fin.cons input Fin.elim0) ht (twoValue (Fin.cons input Fin.elim0))
    obtain ⟨he⟩ := valueUnique tag positionTerm (numeral 3) (Fin.cons input Fin.elim0) ht2
      (show Nonempty (Derivation body (P :: Gamma)
        (graph1 tag (numeral 3) input)) from by
          obtain ⟨htag⟩ := htag
          exact ⟨addHyp htag P⟩)
    rw [positionTermEq] at he
    change Derivation body (P :: Gamma) (eqn (suc (suc z)) (suc (suc (suc z)))) at he
    exact ⟨Derivation.implicationIntroduction (zeroNeSuc (cancelSuc (cancelSuc he)))⟩
  exact InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject (liftP test) guard xs hn

/-- The ORIGINAL result-fold validity AST rejects opening at bottom and
uses its exact normalized old leaf. No successful run or validity is assumed. -/
theorem validatorBottom (node old : Program 2) (input typ parameter : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (graph1 bottomCode input typ)))
    (hl : Nonempty (Derivation body Gamma (graph2 old (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (graph2 (validatorP node old) (suc z) input parameter)) := by
  have hopen := bottomOpeningZero openingGuardP input typ parameter hc
  have hleaf := normalizeAccept old (Fin.cons input (Fin.cons parameter Fin.elim0)) hl
  have h := InternalParameterizedApplicationCertifiedResultFoldClosureLeafProof.leafClosure
    openingGuardP (leafP old) (combineP node) input (suc z) parameter hopen hleaf
  exact andRight h

theorem sourceBottom (data : InternalOriginalUniformDescentSelection.Data)
    (input typ parameter : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (graph1 bottomCode input typ)))
    (hs : Nonempty (Derivation body Gamma (graph2 data.oldSource (suc z) input parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 data.oldTarget (suc z) input parameter))) :
    Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity data) (suc z) input parameter)) :=
  conjunctionAccept (targetP data.oldTarget) (universeP data.oldSource data.member) (Fin.cons input (Fin.cons parameter Fin.elim0))
    (validatorBottom (InternalLessThan.constantOne 2) data.oldTarget input typ parameter hc ht)
    (validatorBottom data.member data.oldSource input typ parameter hc hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
