module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionMinimumCoherenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationTestsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalEqualityTestCompositionProof (equalityOfEqual)
open OriginalVariableDecoderEqualityProof (equalityReject)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalActiveClassKernelBranchProof (equalityControl matrixOfEqual relationFromMatrix)
open OriginalAllPositionAcceptedObserverProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev Old (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed candidate parameter : OTerm alpha) :=
  OriginalActiveClassKernel.Accepted p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P seed candidate parameter
abbrev New (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed candidate parameter : OTerm alpha) := OriginalAllPositionMinimumCoherenceTargets.Accepted p H G W P seed candidate parameter
abbrev Tests (p : GlobalSourcePackage.Inputs) (seed candidate parameter : OTerm alpha) :=
  graph3 (OriginalClassContextAllPositionObserver.allTests p.base.oldRepresentative) (suc z) seed candidate parameter

theorem acceptedRecover (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hh : Nonempty (Derivation body Delta (New p H G W P seed candidate parameter))) :
    Nonempty (Derivation body Delta ((Old p H G W P seed candidate parameter) ⊓ Tests p seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
  let O := OriginalRawSyntaxTransport.variableRankPackedRaw
  let K := OriginalActiveClassKernel.classTest p H G W P
  let C := OriginalClassContextAllPositionSelection.classTest p H G W P
  let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2]
  let E := eqn candidate seed
  apply formulaCases E
  · have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm := matrixOfEqual p H G W O seed candidate parameter (withHyp hd E) he
    have ho := relationFromMatrix p H G W O P seed candidate parameter (withHyp hd E) hm
    have hs := OriginalAllPositionRelationTestsProof.allTestsRefl p.base.oldRepresentative seed parameter (body := body) (Delta := E :: Delta)
    have he' : Nonempty (Derivation body (E :: Delta) (equal seed candidate)) := by
      obtain ⟨h⟩ := he
      simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using
        (show Nonempty (Derivation body (E :: Delta) (eqn seed candidate)) from ⟨InternalTagArithmeticSupportProof.symm h⟩)
    have ht : Nonempty (Derivation body (E :: Delta) (Tests p seed candidate parameter)) := by
      apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 (E :: Delta)
        _ (suc z)
        ![seed,seed,parameter] ![seed,candidate,parameter] _ hs
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change Nonempty (Derivation body (E :: Delta) (equal seed seed))
        simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using
          (show Nonempty (Derivation body (E :: Delta) (eqn seed seed)) from ⟨InternalTagArithmeticSupportProof.refl seed⟩)
      · refine Fin.cases ?_ (fun k => ?_) j
        · change Nonempty (Derivation body (E :: Delta) (equal seed candidate))
          exact he'
        · refine Fin.cases ?_ (fun e => Fin.elim0 e) k
          change Nonempty (Derivation body (E :: Delta) (equal parameter parameter))
          simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using
            (show Nonempty (Derivation body (E :: Delta) (eqn parameter parameter)) from ⟨InternalTagArithmeticSupportProof.refl parameter⟩)
    exact andIntro ho ht
  · have hz := equalityControl (body := body) (Delta := E.not :: Delta) z seed candidate parameter
      (equalityReject candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have hac := binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) seed parameter xs (andRight (withHyp hd E.not)) (projectionValue 0 xs) (projectionValue 2 xs)
    have ho := zeroBranchElim (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (OriginalActiveObservedClass.classTest p H G W O C)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) xs hz (withHyp hh E.not)
    have hc := successorBranchElim A C (OriginalObservedClass.observed O C) (suc z) z xs hac ho
    have hf := conjunctionRecover C (OriginalActiveClassKernel.observerTest O) xs hc
    have hk := activeRecover p H G W K seed candidate parameter (andRight (withHyp hd E.not)) (andLeft hf)
    have hobs := conjunctionAccept K (OriginalActiveClassKernel.observerTest O) xs (andLeft hk) (andRight hf)
    have hwrapped := successorBranchIntro A K (OriginalObservedClass.observed O K) (suc z) z xs hac hobs
    have hresult := zeroBranchIntro (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (OriginalActiveObservedClass.classTest p H G W O K)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2]) (suc z) xs hz hwrapped
    exact andIntro hresult (andRight hk)

theorem acceptedIntro (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hh : Nonempty (Derivation body Delta (Old p H G W P seed candidate parameter)))
    (ht : Nonempty (Derivation body Delta (Tests p seed candidate parameter))) :
    Nonempty (Derivation body Delta (New p H G W P seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
  let O := OriginalRawSyntaxTransport.variableRankPackedRaw
  let K := OriginalActiveClassKernel.classTest p H G W P
  let C := OriginalClassContextAllPositionSelection.classTest p H G W P
  let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2]
  let E := eqn candidate seed
  apply formulaCases E
  · have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := equalityControl (suc z) seed candidate parameter (equalityOfEqual candidate seed he)
    have htarget := binaryValue (OriginalTypedDecoder.target H G) (.projection 0) (.projection 2)
      (suc z) seed parameter xs (andLeft (withHyp hd E)) (projectionValue 0 xs) (projectionValue 2 xs)
    exact successorBranchIntro (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (OriginalActiveObservedClass.classTest p H G W O C)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) z xs hc htarget
  · have hz := equalityControl (body := body) (Delta := E.not :: Delta) z seed candidate parameter
      (equalityReject candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have hac := binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) seed parameter xs (andRight (withHyp hd E.not)) (projectionValue 0 xs) (projectionValue 2 xs)
    have ho := zeroBranchElim (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (OriginalActiveObservedClass.classTest p H G W O K)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) xs hz (withHyp hh E.not)
    have hc := successorBranchElim A K (OriginalObservedClass.observed O K) (suc z) z xs hac ho
    have hf := conjunctionRecover K (OriginalActiveClassKernel.observerTest O) xs hc
    have hk := activeIntro p H G W K seed candidate parameter (andRight (withHyp hd E.not)) (andLeft hf) (withHyp ht E.not)
    have hobs := conjunctionAccept C (OriginalActiveClassKernel.observerTest O) xs hk (andRight hf)
    have hwrapped := successorBranchIntro A C (OriginalObservedClass.observed O C) (suc z) z xs hac hobs
    have hresult := zeroBranchIntro (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (OriginalActiveObservedClass.classTest p H G W O C)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2]) (suc z) xs hz hwrapped
    exact hresult

theorem characterizationAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter))) :
    Nonempty (Derivation body Delta ((New p H G W P seed candidate parameter).iff
      ((Old p H G W P seed candidate parameter) ⊓ Tests p seed candidate parameter))) := by
  let A := New p H G W P seed candidate parameter
  let B := Old p H G W P seed candidate parameter ⊓ Tests p seed candidate parameter
  obtain ⟨hf⟩ := acceptedRecover p H G W P seed candidate parameter (withHyp hd A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := acceptedIntro p H G W P seed candidate parameter (withHyp hd B) (andLeft hb) (andRight hb)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hr)⟩

theorem actualHitDomain (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (seed other parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hh : Nonempty (Derivation body Delta (New p H G W P seed other parameter))) :
    Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W other parameter)) :=
  OriginalActiveClassKernelInternalProof.hitDomainAt p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P seed other parameter hd
    (andLeft (acceptedRecover p H G W P seed other parameter hd hh))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
