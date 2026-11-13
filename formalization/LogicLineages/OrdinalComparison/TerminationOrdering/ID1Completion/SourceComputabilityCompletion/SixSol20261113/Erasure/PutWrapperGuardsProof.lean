module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutIntegrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNonApplicationSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutWrapperGuardsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject numeralNe numeralNeApply)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroNotOne {n : Nat} (p : Program n) (xs : Fin n → OTerm alpha)
    (hz : Nonempty (Derivation body Delta (programGraph p z xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs).not) := by
  let A := programGraph p (suc z) xs
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := valueUnique p (suc z) z xs h (withHyp hz A)
  exact ⟨Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.sucNeZeroApply he)⟩

theorem conjunctionNotLeft {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (programGraph p (suc z) xs).not)) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.conjunction p q) (suc z) xs).not) := by
  let A := programGraph (InternalAcceptance.conjunction p q) (suc z) xs
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hp⟩ := andLeft (conjunctionRecover p q xs h)
  obtain ⟨hn⟩ := withHyp hn A
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hp)⟩

theorem conjunctionNotRight {n : Nat} (p q : Program n) (xs : Fin n → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (programGraph q (suc z) xs).not)) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.conjunction p q) (suc z) xs).not) := by
  let A := programGraph (InternalAcceptance.conjunction p q) (suc z) xs
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hq⟩ := andRight (conjunctionRecover p q xs h)
  obtain ⟨hn⟩ := withHyp hn A
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hq)⟩

theorem packedTag (s typ raw head base : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base))) :
    Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons s Fin.elim0
  have hr := unaryValue InternalUnpair.right (.projection 0) raw s xs
    (pairRight s typ raw hp) (projectionValue 0 xs)
  exact OriginalRawSyntaxTransportInternalConstructorFieldsProof.ordinaryTag
    (rightOf (.projection 0)) raw head base xs hr ho

theorem notBottom (s : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s))) :
    Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not) := by
  let A := BottomRepresentative.bottomGraph (suc z) s
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h3 := OriginalTransparentLambdaValidityInternalBottomShapeProof.bottomTag s h
  obtain ⟨he⟩ := valueUnique OriginalLambdaConstructor.tag (numeral 4) (numeral 3)
    (Fin.cons s Fin.elim0) (withHyp ht A) h3
  exact ⟨Derivation.implicationIntroduction (numeralNeApply 4 3 (by decide) he)⟩

theorem variableZero (s t cert parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s))) :
    Nonempty (Derivation body Delta (graph4 OriginalConstructorLeaf.variableAt z s t cert parameter)) := by
  let us : Fin 1 → OTerm alpha := Fin.cons s Fin.elim0
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  have hv := sameReject OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1)
    (numeral 4) z us ht (constantZeroValue us) (numeralNe 4 0 (by decide))
  exact unaryValue OriginalConstructorLeaf.variableTest (.projection 0) z s xs hv (projectionValue 0 xs)

theorem lambdaZero (s t cert parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s))) :
    Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sourceLambda z s t cert parameter)) := by
  let us : Fin 1 → OTerm alpha := Fin.cons s Fin.elim0
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  have hv := sameReject OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
    (numeral 4) (suc z) us ht (InternalLessThanSupportProof.oneConstantValue us) (numeralNe 4 1 (by decide))
  exact unaryValue OriginalLambdaGuardLeaf.lambdaTest (.projection 0) z s xs hv (projectionValue 0 xs)

theorem neutralZero (s t cert parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s))) :
    Nonempty (Derivation body Delta (graph4 OriginalNeutralLeaf.neutralAt z s t cert parameter)) := by
  let us : Fin 1 → OTerm alpha := Fin.cons s Fin.elim0
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  have hv := sameReject OriginalLambdaConstructor.tag (two 1) (numeral 4) (numeral 2)
    us ht (twoValue us) (numeralNe 4 2 (by decide))
  have hn := conjunctionNotLeft (InternalApplicationStepPeel.same OriginalLambdaConstructor.tag (two 1))
    (InternalAcceptance.branch OriginalNeutralLeaf.lambdaFunctionTest
      (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)) us
    (zeroNotOne _ us hv)
  have hz := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _ us hn
  exact unaryValue OriginalNeutralLeaf.neutralTest (.projection 0) z s xs hz (projectionValue 0 xs)

theorem wrapper (endpoint : Program 6) (window : Program 1) (leaf : Program 4)
    (s t cert parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 4) s)))
    (hl : Nonempty (Derivation body Delta (graph4 leaf (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalHereditaryLambdaGlobal.wrapper endpoint window leaf) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  have hspine := OriginalTransparentDirectBottomNonApplicationSpineProof.tagSpine
    s t cert parameter (numeral 4) ht (numeralNe 2 4 (by decide)) (numeralNe 4 3 (by decide))
  have hn := zeroNotOne OriginalNeutralLeaf.neutralAt xs (neutralZero s t cert parameter ht)
  have htr : Nonempty (Derivation body Delta
      (graph4 (OriginalNeutralLeaf.trigger endpoint window) (suc z) s t cert parameter).not) :=
    conjunctionNotRight (OriginalNeutralLeaf.windowAt window) _ xs
    (conjunctionNotLeft OriginalNeutralLeaf.neutralAt _ xs hn)
  have htr0 := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _ xs htr
  have hneutral : Nonempty (Derivation body Delta
      (graph4 (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) s t cert parameter)) :=
    zeroBranchIntro (OriginalNeutralLeaf.trigger endpoint window) _ _ (suc z) xs
    htr0 (InternalLessThanSupportProof.oneConstantValue xs)
  have hv : Nonempty (Derivation body Delta
      (graph4 OriginalConstructorLeaf.variableGuard (suc z) s t cert parameter)) :=
    zeroBranchIntro _ _ _ (suc z) xs
    (normalizeReject OriginalConstructorLeaf.variableAt xs
      (zeroNotOne _ xs (variableZero s t cert parameter ht)))
    (InternalLessThanSupportProof.oneConstantValue xs)
  have hb := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs (notBottom s ht)
  exact conjunctionAccept _ _ xs
    (conjunctionAccept _ _ xs (conjunctionAccept _ _ xs hl hspine) hneutral)
    (conjunctionAccept _ _ xs hb hv)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutWrapperGuardsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutWrapperGuardsProof
