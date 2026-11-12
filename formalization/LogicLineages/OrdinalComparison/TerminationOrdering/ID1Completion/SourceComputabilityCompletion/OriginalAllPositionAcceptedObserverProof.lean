module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalRecursionClosureLogicProof InternalPositiveUnfoldingSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalSquareRootArithmeticSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalClassContextAllPositionObserver
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem emptyTests (R : Program 2) (seed candidate parameter : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right z parameter))) :
    Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (allTests R) (suc z) seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
  have hc := unaryValue InternalUnpair.right (.projection 2) z parameter xs hg (projectionValue 2 xs)
  have hn := unaryValue length (rightOf (.projection 2)) z z xs lengthZero hc
  exact compositionValue (scan R)
    ![.composition length (fun _ : Fin 1 => rightOf (.projection 2)),.projection 0,.projection 1,.projection 2]
    (suc z) xs (Fin.cons z (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))))
    (OriginalAllPositionRelationScanStepProof.zeroAccepted R seed candidate parameter)
    (fun i => Fin.cases hn (Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k)))) i)

theorem activeRecoverAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed candidate parameter gamma : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hh : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta ((OriginalTransparentMinimum.graph3 P (suc z) seed candidate parameter) ⊓
      OriginalTransparentMinimum.graph3 (allTests p.base.oldRepresentative) (suc z) seed candidate parameter)) := by
  apply zeroSuccessorCases Delta gamma _
  · let E := eqn gamma z
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := outputTransport InternalUnpair.right gamma z (Fin.cons parameter Fin.elim0) he (withHyp hg E)
    let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
    let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2]
    have hc := unaryValue InternalUnpair.right (.projection 2) z parameter xs hz (projectionValue 2 xs)
    have hp := zeroBranchElim (rightOf (.projection 2)) P
      (InternalAcceptance.branch A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative)))
      (suc z) xs hc (withHyp hh E)
    exact andIntro hp (emptyTests p.base.oldRepresentative seed candidate parameter hz)
  · intro beta j Theta tail hj he
    have ha' := renameInto ha j Theta hj
    have hg' := renameInto hg j Theta hj
    have hh' := renameInto hh j Theta hj
    simp only [graph1Rename,graph2Rename,OriginalTransparentMinimum.graph3,programRename,consTermRename,emptyRename,conjunctionRename,
      InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at ha' hg' hh' ⊢
    let xs : Fin 3 → OTerm beta := ![seed.relabel j,candidate.relabel j,parameter.relabel j]
    let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2]
    have hgs := outputTransport InternalUnpair.right (gamma.relabel j) (suc tail) (Fin.cons (parameter.relabel j) Fin.elim0) he hg'
    have hc := unaryValue InternalUnpair.right (.projection 2) (suc tail) (parameter.relabel j) xs hgs (projectionValue 2 xs)
    have hb := successorBranchElim (rightOf (.projection 2)) P
      (InternalAcceptance.branch A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative))) (suc z) tail xs hc hh'
    have hac := binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) (seed.relabel j) (parameter.relabel j) xs ha' (projectionValue 0 xs) (projectionValue 2 xs)
    exact conjunctionRecover P (allTests p.base.oldRepresentative) xs
      (successorBranchElim A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative)) (suc z) z xs hac hb)

theorem activeIntroAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed candidate parameter gamma : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hp : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 P (suc z) seed candidate parameter)))
    (ht : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (allTests p.base.oldRepresentative) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter)) := by
  apply zeroSuccessorCases Delta gamma _
  · let E := eqn gamma z
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := outputTransport InternalUnpair.right gamma z (Fin.cons parameter Fin.elim0) he (withHyp hg E)
    let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
    let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2]
    exact zeroBranchIntro (rightOf (.projection 2)) P
      (InternalAcceptance.branch A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative)))
      (suc z) xs (unaryValue InternalUnpair.right (.projection 2) z parameter xs hz (projectionValue 2 xs)) (withHyp hp E)
  · intro beta j Theta tail hj he
    have ha' := renameInto ha j Theta hj
    have hg' := renameInto hg j Theta hj
    have hp' := renameInto hp j Theta hj
    have ht' := renameInto ht j Theta hj
    simp only [graph1Rename,graph2Rename,OriginalTransparentMinimum.graph3,programRename,consTermRename,emptyRename,
      InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at ha' hg' hp' ht' ⊢
    let xs : Fin 3 → OTerm beta := ![seed.relabel j,candidate.relabel j,parameter.relabel j]
    let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2]
    have hgs := outputTransport InternalUnpair.right (gamma.relabel j) (suc tail) (Fin.cons (parameter.relabel j) Fin.elim0) he hg'
    have hc := unaryValue InternalUnpair.right (.projection 2) (suc tail) (parameter.relabel j) xs hgs (projectionValue 2 xs)
    have hac := binaryValue (OriginalActiveObservedClass.activation p H G W) (.projection 0) (.projection 2)
      (suc z) (seed.relabel j) (parameter.relabel j) xs ha' (projectionValue 0 xs) (projectionValue 2 xs)
    exact successorBranchIntro (rightOf (.projection 2)) P
      (InternalAcceptance.branch A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative))) (suc z) tail xs hc
      (successorBranchIntro A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative)) (suc z) z xs hac
        (conjunctionAccept P (allTests p.base.oldRepresentative) xs hp' ht'))

theorem activeRecover (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))

    (hh : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta ((OriginalTransparentMinimum.graph3 P (suc z) seed candidate parameter) ⊓
      OriginalTransparentMinimum.graph3 (allTests p.base.oldRepresentative) (suc z) seed candidate parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons parameter Fin.elim0) _
  intro beta j Theta gamma hj hg
  have ha' := renameInto ha j Theta hj
  have hh' := renameInto hh j Theta hj
  simp only [graph1Rename,graph2Rename,OriginalTransparentMinimum.graph3,programRename,consTermRename,emptyRename,conjunctionRename,
    InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at ha' hh' hg ⊢
  exact activeRecoverAt p H G W P (seed.relabel j) (candidate.relabel j) (parameter.relabel j) gamma ha' hg hh'

theorem activeIntro (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed candidate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))

    (hp : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 P (suc z) seed candidate parameter)))
    (ht : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (allTests p.base.oldRepresentative) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons parameter Fin.elim0) _
  intro beta j Theta gamma hj hg
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,OriginalTransparentMinimum.graph3,programRename,consTermRename,emptyRename,conjunctionRename,
    InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at ha' hp' ht' hg ⊢
  exact activeIntroAt p H G W P (seed.relabel j) (candidate.relabel j) (parameter.relabel j) gamma ha' hg hp' ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedObserverProof
