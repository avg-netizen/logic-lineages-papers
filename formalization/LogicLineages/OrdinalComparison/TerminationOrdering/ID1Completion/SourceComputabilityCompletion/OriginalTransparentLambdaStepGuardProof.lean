module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe numeralNeApply sameReject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rejectAtZero {n : Nat} (p : Program n) (xs : Fin n → OTerm alpha)
    (hz : Nonempty (Derivation body Delta (programGraph p z xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs).not) := by
  let P := programGraph p (suc z) xs
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := valueUnique p (suc z) z xs hp (withHyp hz P)
  exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.sucNeZeroApply he)⟩

/-- Lambda tag one excludes actual bottom tag three. -/
theorem notBottom (s : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) s))) :
    Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not) := by
  let P := BottomRepresentative.bottomGraph (suc z) s
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hthree := OriginalTransparentLambdaValidityInternalBottomShapeProof.bottomTag s hp
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (suc z) (numeral 3)
    (Fin.cons s Fin.elim0) (withHyp htag P) hthree
  exact ⟨Derivation.implicationIntroduction (numeralNeApply 1 3 (by decide) he)⟩

/-- A lambda cannot activate the neutral tag-two trigger. -/
theorem neutralReject (endpoint : Program 6) (window : Program 1)
    (xs : Fin 4 → OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) (xs 0)))) :
    Nonempty (Derivation body Delta (programGraph (OriginalNeutralLeaf.trigger endpoint window) (suc z) xs).not) := by
  let P := programGraph (OriginalNeutralLeaf.trigger endpoint window) (suc z) xs
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha := andRight (conjunctionRecover (OriginalNeutralLeaf.windowAt window) _ xs hp)
  have hb := andLeft (conjunctionRecover OriginalNeutralLeaf.neutralAt _ xs ha)
  have hc := unaryRecover OriginalNeutralLeaf.neutralTest (.projection 0) (suc z) (xs 0) xs hb (projectionValue 0 xs)
  have hd := andLeft (conjunctionRecover
    (InternalApplicationStepPeel.same (InternalApplicationStepPeel.constructorTag (.projection 0))
      (InternalApplicationCertificateConstructors.two 1)) _ (Fin.cons (xs 0) Fin.elim0) hc)
  have htwo := InternalStructuralEndpointGuardSupportProof.sameRightRecover
    OriginalLambdaConstructor.tag (InternalApplicationCertificateConstructors.two 1) (numeral 2)
    (Fin.cons (xs 0) Fin.elim0) hd (twoValue (Fin.cons (xs 0) Fin.elim0))
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 2) (suc z)
    (Fin.cons (xs 0) Fin.elim0) htwo (withHyp htag P)
  exact ⟨Derivation.implicationIntroduction (numeralNeApply 2 1 (by decide) he)⟩

theorem guards (endpoint : Program 6) (window : Program 1) (s t cert parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc z) s))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) s t cert parameter ⊓
        graph4 (InternalAcceptance.conjunction
          (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
          OriginalConstructorLeaf.variableGuard) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have htrigger := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
    (OriginalNeutralLeaf.windowAt window) _ xs (neutralReject endpoint window xs htag)
  have hneutral : Nonempty (Derivation body Delta
      (programGraph (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) xs)) := zeroBranchIntro _ _ _ (suc z) xs htrigger (InternalLessThanSupportProof.oneConstantValue xs)
  have hvar := sameReject OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1)
    (suc z) z (Fin.cons s Fin.elim0) htag (constantZeroValue _) (numeralNe 1 0 (by decide))
  have hvarAt := unaryValue OriginalConstructorLeaf.variableTest (.projection 0) z s xs hvar (projectionValue 0 xs)
  have hvariable : Nonempty (Derivation body Delta
      (programGraph OriginalConstructorLeaf.variableGuard (suc z) xs)) := zeroBranchIntro _ _ _ (suc z) xs
    (normalizeReject OriginalConstructorLeaf.variableAt xs (rejectAtZero OriginalConstructorLeaf.variableAt xs hvarAt))
    (InternalLessThanSupportProof.oneConstantValue xs)
  have hnonbottom := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs (notBottom s htag)
  exact andIntro hneutral (conjunctionAccept _ _ xs hnonbottom hvariable)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGuardProof
