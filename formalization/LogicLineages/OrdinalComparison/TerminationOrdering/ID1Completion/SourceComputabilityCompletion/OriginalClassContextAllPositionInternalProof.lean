module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalRecursionClosureLogicProof InternalPositiveUnfoldingSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalSquareRootArithmeticSupportProof
open InternalOriginalUniformVertexPathSupportProof (ternaryValue ternaryRecover)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalClassContextAllPositionObserver
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal equality-test exposure at one index; no evaluation reflection. -/
theorem positionOutputIff (R : Program 2) (cutoff seed candidate parameter value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta
      (graph4 (positionTest R) (suc z) cutoff seed candidate parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalTransparentMinimum.graph3 (positionObservation R) value cutoff seed parameter).iff
       (OriginalTransparentMinimum.graph3 (positionObservation R) value cutoff candidate parameter))) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons cutoff (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0)))
  let A := OriginalTransparentMinimum.graph3 (positionObservation R) value cutoff seed parameter
  let B := OriginalTransparentMinimum.graph3 (positionObservation R) value cutoff candidate parameter
  have forward : Nonempty (Derivation body (A :: Delta) B) := by
    have hv : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hleft := ternaryValue (positionObservation R) (.projection 0) (.projection 1) (.projection 3)
      value cutoff seed parameter xs hv (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 3 xs)
    have hright := OriginalObservedClassProof.sameKnownLeft
      (.composition (positionObservation R) ![.projection 0,.projection 1,.projection 3])
      (.composition (positionObservation R) ![.projection 0,.projection 2,.projection 3])
      value xs (withHyp ht A) hleft
    exact ternaryRecover (positionObservation R) (.projection 0) (.projection 2) (.projection 3)
      value cutoff candidate parameter xs hright (projectionValue 0 xs) (projectionValue 2 xs) (projectionValue 3 xs)
  have backward : Nonempty (Derivation body (B :: Delta) A) := by
    have hv : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hright := ternaryValue (positionObservation R) (.projection 0) (.projection 2) (.projection 3)
      value cutoff candidate parameter xs hv (projectionValue 0 xs) (projectionValue 2 xs) (projectionValue 3 xs)
    have hleft := OriginalObservedClassProof.sameKnownRight
      (.composition (positionObservation R) ![.projection 0,.projection 1,.projection 3])
      (.composition (positionObservation R) ![.projection 0,.projection 2,.projection 3])
      value xs (withHyp ht B) hright
    exact ternaryRecover (positionObservation R) (.projection 0) (.projection 1) (.projection 3)
      value cutoff seed parameter xs hleft (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 3 xs)
  obtain ⟨hf⟩ := forward
  obtain ⟨hb⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem allTestsAtSuccessor (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed candidate parameter gamma tail : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hg : Nonempty (Derivation body Delta
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0))))
    (he : Nonempty (Derivation body Delta (eqn gamma (suc tail))))
    (hh : Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (allTests p.base.oldRepresentative) (suc z) seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W)
    ![.projection 0,.projection 2]
  let B := InternalAcceptance.branch A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative))
  have hgs := outputTransport InternalUnpair.right gamma (suc tail) (Fin.cons parameter Fin.elim0) he hg
  have hc := unaryValue InternalUnpair.right (.projection 2) (suc tail) parameter xs hgs (projectionValue 2 xs)
  have hbranch := successorBranchElim (rightOf (.projection 2)) P B (suc z) tail xs hc hh
  have hac := binaryValue (OriginalActiveObservedClass.activation p H G W)
    (.projection 0) (.projection 2) (suc z) seed parameter xs ha (projectionValue 0 xs) (projectionValue 2 xs)
  have hconj := successorBranchElim A P (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative))
    (suc z) z xs hac hbranch
  exact andRight (conjunctionRecover P (allTests p.base.oldRepresentative) xs hconj)

/-- The empty branch is excluded by genuine arithmetic: length(nil)=0 and
nothing lies below zero. No native positivity is used. -/
theorem allTestsHit (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed candidate parameter gamma count cutoff : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hg : Nonempty (Derivation body Delta
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0))))
    (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
    (hb : Nonempty (Derivation body Delta (Below cutoff count)))
    (hh : Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (allTests p.base.oldRepresentative) (suc z) seed candidate parameter)) := by
  apply zeroSuccessorCases Delta gamma _
  · have he : Nonempty (Derivation body (eqn gamma z :: Delta) (eqn gamma z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := headTransport length count gamma z Fin.elim0 he (withHyp hl (eqn gamma z))
    obtain ⟨hc⟩ := lengthNilRecover count hz
    obtain ⟨hbelow⟩ := withHyp hb (eqn gamma z)
    obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha cutoff
    exact ⟨Derivation.explosion (Derivation.implicationElimination
      (weakenClosed hn _) (orderRight cutoff hc hbelow))⟩
  · intro beta j Theta tail hj he
    have ha' := renameInto ha j Theta hj
    have hg' := renameInto hg j Theta hj
    have hh' := renameInto hh j Theta hj
    simp only [programRename,consTermRename,emptyRename,graph2Rename,
      OriginalTransparentMinimum.graph3,InternalTagArithmeticSyntaxProof.sucRelabel,
      InternalTagArithmeticSyntaxProof.zRelabel] at ha' hg' hh' ⊢
    exact allTestsAtSuccessor p H G W P (seed.relabel j) (candidate.relabel j)
      (parameter.relabel j) (gamma.relabel j) tail ha' hg' he hh'

theorem scanHit (R : Program 2) (seed candidate parameter gamma count : OTerm alpha)
    (hg : Nonempty (Derivation body Delta
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0))))
    (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
    (hh : Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (allTests R) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  have hc := unaryValue InternalUnpair.right (.projection 2) gamma parameter xs hg (projectionValue 2 xs)
  have hn := unaryValue length (rightOf (.projection 2)) count gamma xs hl hc
  apply compositionRecover (scan R)
    ![.composition length (fun _ : Fin 1 => rightOf (.projection 2)),.projection 0,.projection 1,.projection 2]
    (suc z) xs (Fin.cons count (Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0)))) hh
  intro i
  exact Fin.cases hn (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q)))) i
theorem actualHit : OriginalClassContextAllPositionObserverTargets.Hit := by
  intro p H G W P body alpha Delta seed candidate parameter gamma count cutoff value
  let A := graph2 (OriginalActiveObservedClass.activation p H G W)
      InternalOriginalStepGuard.one seed parameter ⊓
    (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
    (lengthGraph count gamma ⊓ (Below cutoff count ⊓
      OriginalTransparentMinimum.graph3 (classTest p H G W P)
        InternalOriginalStepGuard.one seed candidate parameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha := andLeft h
  have hg := andLeft (andRight h)
  have hl := andLeft (andRight (andRight h))
  have hb := andLeft (andRight (andRight (andRight h)))
  have hh := andRight (andRight (andRight (andRight h)))
  have hall := allTestsHit p H G W P seed candidate parameter gamma count cutoff ha hg hl hb hh
  have hscan := scanHit p.base.oldRepresentative seed candidate parameter gamma count hg hl hall
  have hposition := OriginalClassContextAllPositionScanProof.exposeAt
    p.base.oldRepresentative count cutoff seed candidate parameter hscan hb
  obtain ⟨hout⟩ := positionOutputIff p.base.oldRepresentative cutoff seed candidate parameter value hposition
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionInternalProof
