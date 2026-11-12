module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaStoppedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardsProof
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

theorem notBottom (s : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s))) :
    Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not) := by
  let P := BottomRepresentative.bottomGraph (suc z) s
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hthree := OriginalTransparentLambdaValidityInternalBottomShapeProof.bottomTag s hp
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (suc (suc z)) (numeral 3)
    (Fin.cons s Fin.elim0) (withHyp htag P) hthree
  exact ⟨Derivation.implicationIntroduction (numeralNeApply 2 3 (by decide) he)⟩

theorem neutralReject (endpoint : Program 6) (window : Program 1)
 (xs : Fin 4 → OTerm alpha)
 (hg : Nonempty (Derivation body Delta (programGraph (OriginalNeutralLeaf.guardAt endpoint) (suc z) xs))) :
 Nonempty (Derivation body Delta (programGraph (OriginalNeutralLeaf.trigger endpoint window) (suc z) xs).not) := by
 let P := programGraph (OriginalNeutralLeaf.trigger endpoint window) (suc z) xs
 have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have ha := andRight (conjunctionRecover (OriginalNeutralLeaf.windowAt window) _ xs hp)
 have he := andRight (conjunctionRecover OriginalNeutralLeaf.neutralAt _ xs ha)
 have hz := InternalStructuralEndpointGuardSupportProof.sameRightRecover
  (OriginalNeutralLeaf.guardAt endpoint) (InternalAcceptance.constantZero 4) z xs he (constantZeroValue xs)
 obtain ⟨hbad⟩ := valueUnique (OriginalNeutralLeaf.guardAt endpoint) (suc z) z xs (withHyp hg P) hz
 exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.sucNeZeroApply hbad)⟩

theorem guards (endpoint : Program 6) (window : Program 1) (s t cert parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s)))
    (hguard : Nonempty (Derivation body Delta (graph4 (OriginalNeutralLeaf.guardAt endpoint) (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) s t cert parameter ⊓
        graph4 (InternalAcceptance.conjunction
          (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
          OriginalConstructorLeaf.variableGuard) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have htrigger := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
    (OriginalNeutralLeaf.windowAt window) _ xs (neutralReject endpoint window xs hguard)
  have hneutral : Nonempty (Derivation body Delta
      (programGraph (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) xs)) := zeroBranchIntro _ _ _ (suc z) xs htrigger (InternalLessThanSupportProof.oneConstantValue xs)
  have hvar := sameReject OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1)
    (suc (suc z)) z (Fin.cons s Fin.elim0) htag (constantZeroValue _) (numeralNe 2 0 (by decide))
  have hvarAt := unaryValue OriginalConstructorLeaf.variableTest (.projection 0) z s xs hvar (projectionValue 0 xs)
  have hvariable : Nonempty (Derivation body Delta
      (programGraph OriginalConstructorLeaf.variableGuard (suc z) xs)) := zeroBranchIntro _ _ _ (suc z) xs
    (normalizeReject OriginalConstructorLeaf.variableAt xs (rejectAtZero OriginalConstructorLeaf.variableAt xs hvarAt))
    (InternalLessThanSupportProof.oneConstantValue xs)
  have hnonbottom := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs (notBottom s htag)
  exact andIntro hneutral (conjunctionAccept _ _ xs hnonbottom hvariable)
theorem stopAtApplication (s t cert parameter : OTerm alpha)
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s))) :
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.stop (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have ht := sameReject OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
  (suc (suc z)) (suc z) ![s] htag (InternalLessThanSupportProof.oneConstantValue _) (numeralNe 2 1 (by decide))
 have hs := unaryValue OriginalLambdaConstructor.lambdaTest (.projection 0) z s xs ht (projectionValue 0 xs)
 exact zeroBranchIntro (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalLambdaGuardLeaf.sourceLambda)
  (InternalLessThan.constantOne 4)
  (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalLambdaGuardLeaf.sameBottom)
  (suc z) xs (normalizeReject OriginalLambdaGuardLeaf.sourceLambda xs (rejectAtZero _ xs hs))
  (InternalLessThanSupportProof.oneConstantValue xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardsProof
