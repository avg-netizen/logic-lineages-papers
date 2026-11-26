module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalEqualityTestCompositionProof (equalityOfEqual)
open OriginalVariableDecoderEqualityProof (equalityReject)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open OriginalActiveClassKernel OriginalActiveClassKernelEqualityProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev Matrix (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (seed candidate parameter : OTerm alpha) : Formula alpha :=
  Domain p H G W candidate parameter ⊓
    (keyGraph p.base.oldRepresentative seed candidate parameter ⊓
      observerGraph O seed candidate parameter)

abbrev wrappedClass (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) : Program 3 :=
  OriginalActiveObservedClass.classTest p H G W O (classTest p H G W P)

theorem domainValue (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (seed parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter))) :
    Nonempty (Derivation body Delta (graph2 (domainProgram p H G W) (suc z) seed parameter)) :=
  conjunctionAccept (OriginalTypedDecoder.target H G) (OriginalActiveObservedClass.activation p H G W)
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) (andLeft hd) (andRight hd)

theorem domainRecover (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (seed parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 (domainProgram p H G W) (suc z) seed parameter))) :
    Nonempty (Derivation body Delta (Domain p H G W seed parameter)) :=
  conjunctionRecover (OriginalTypedDecoder.target H G) (OriginalActiveObservedClass.activation p H G W)
    (Fin.cons seed (Fin.cons parameter Fin.elim0)) hd

theorem domainOfEqual (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
    Nonempty (Derivation body Delta (Domain p H G W candidate parameter)) := by
  obtain ⟨he⟩ := he
  exact andIntro
    (headTransport (OriginalTypedDecoder.target H G) (suc z) seed candidate
      (Fin.cons parameter Fin.elim0) ⟨symm he⟩ (andLeft hd))
    (headTransport (OriginalActiveObservedClass.activation p H G W) (suc z) seed candidate
      (Fin.cons parameter Fin.elim0) ⟨symm he⟩ (andRight hd))

theorem matrixOfEqual (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
    Nonempty (Derivation body Delta (Matrix p H G W O seed candidate parameter)) :=
  andIntro (domainOfEqual p H G W seed candidate parameter hd he)
    (andIntro (keyOfEqual p.base.oldRepresentative seed candidate parameter he)
      (OriginalActiveClassKernelEqualityProof.observerOfEqual O seed candidate parameter he))

/-- On an active seed, both literal active wrappers select their guarded
branches. Their actual conjunction graphs expose the candidate domain, the
pre-minimum key comparison and the original observer comparison. -/
theorem matrixFromObserved (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph3 (wrappedClass p H G W O P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta (Matrix p H G W O seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W)
    ![.projection 0,.projection 2]
  let C := classTest p H G W P
  have hact : Nonempty (Derivation body Delta (programGraph A (suc z) xs)) :=
    binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) seed parameter xs ha (projectionValue 0 xs) (projectionValue 2 xs)
  have ho := successorBranchElim A C (OriginalObservedClass.observed O C) (suc z) z xs hact hr
  have hf := conjunctionRecover C (observerTest O) xs ho
  have hk := successorBranchElim A P (kernel p H G W) (suc z) z xs hact (andLeft hf)
  have hc := conjunctionRecover
    (.composition (domainProgram p H G W) ![.projection 1,.projection 2])
    (keyTest p.base.oldRepresentative) xs hk
  have hd := binaryRecover (domainProgram p H G W) (.projection 1) (.projection 2)
    (suc z) candidate parameter xs (andLeft hc) (projectionValue 1 xs) (projectionValue 2 xs)
  exact andIntro (domainRecover p H G W candidate parameter hd)
    (andIntro (andRight hc) (andRight hf))

theorem observedFromMatrix (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hm : Nonempty (Derivation body Delta (Matrix p H G W O seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (graph3 (wrappedClass p H G W O P) (suc z) seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W)
    ![.projection 0,.projection 2]
  let C := classTest p H G W P
  have hact : Nonempty (Derivation body Delta (programGraph A (suc z) xs)) :=
    binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) seed parameter xs ha (projectionValue 0 xs) (projectionValue 2 xs)
  have hd := binaryValue (domainProgram p H G W) (.projection 1) (.projection 2)
    (suc z) candidate parameter xs (domainValue p H G W candidate parameter (andLeft hm))
      (projectionValue 1 xs) (projectionValue 2 xs)
  have hk := conjunctionAccept
    (.composition (domainProgram p H G W) ![.projection 1,.projection 2])
    (keyTest p.base.oldRepresentative) xs hd (andLeft (andRight hm))
  have hc := successorBranchIntro A P (kernel p H G W) (suc z) z xs hact hk
  have ho := conjunctionAccept C (observerTest O) xs hc (andRight (andRight hm))
  exact successorBranchIntro A C (OriginalObservedClass.observed O C) (suc z) z xs hact ho

theorem equalityControl (out seed candidate parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.equalityTest out candidate seed))) :
    Nonempty (Derivation body Delta
      (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
        out seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  exact binaryValue InternalEqualityTest.equalityTest (.projection 1) (.projection 0)
    out candidate seed xs he (projectionValue 1 xs) (projectionValue 0 xs)

theorem matrixFromRelation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hr : Nonempty (Derivation body Delta (Accepted p H G W O P seed candidate parameter))) :
    Nonempty (Derivation body Delta (Matrix p H G W O seed candidate parameter)) := by
  apply formulaCases (eqn candidate seed)
  · exact matrixOfEqual p H G W O seed candidate parameter (withHyp hd (eqn candidate seed))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  · let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
    have hz : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
          z seed candidate parameter)) := equalityControl z seed candidate parameter
      (equalityReject candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (wrappedClass p H G W O P) (suc z) seed candidate parameter)) := zeroBranchElim
      (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (wrappedClass p H G W O P)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) xs hz (withHyp hr (eqn candidate seed).not)
    exact matrixFromObserved p H G W O P seed candidate parameter
      (andRight (withHyp hd (eqn candidate seed).not)) ho

theorem relationFromMatrix (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (O : Program 1) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (Domain p H G W seed parameter)))
    (hm : Nonempty (Derivation body Delta (Matrix p H G W O seed candidate parameter))) :
    Nonempty (Derivation body Delta (Accepted p H G W O P seed candidate parameter)) := by
  apply formulaCases (eqn candidate seed)
  · let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
    have he : Nonempty (Derivation body (eqn candidate seed :: Delta)
        (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
          (suc z) seed candidate parameter)) := equalityControl (suc z) seed candidate parameter
      (equalityOfEqual candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ht : Nonempty (Derivation body (eqn candidate seed :: Delta)
        (programGraph (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
          (suc z) xs)) := binaryValue (OriginalTypedDecoder.target H G) (.projection 0) (.projection 2)
      (suc z) seed parameter xs (andLeft (withHyp hd (eqn candidate seed)))
        (projectionValue 0 xs) (projectionValue 2 xs)
    exact successorBranchIntro
      (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (wrappedClass p H G W O P)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) z xs he ht
  · let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
    have hz : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
          z seed candidate parameter)) := equalityControl z seed candidate parameter
      (equalityReject candidate seed ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have ho : Nonempty (Derivation body ((eqn candidate seed).not :: Delta)
        (graph3 (wrappedClass p H G W O P) (suc z) seed candidate parameter)) :=
      observedFromMatrix p H G W O P seed candidate parameter
        (andRight (withHyp hd (eqn candidate seed).not)) (withHyp hm (eqn candidate seed).not)
    exact zeroBranchIntro
      (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
      (wrappedClass p H G W O P)
      (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
      (suc z) xs hz ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
