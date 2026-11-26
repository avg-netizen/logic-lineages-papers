module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalSquareRootArithmeticSupportProof InternalAdditionLawsProof InternalUnpairArithmeticProof
open InternalPositiveUnfoldingSupportProof
open PrimaryUncoveredCount
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromWeak (a b : OTerm alpha) (h : Nonempty (Derivation body Delta (ltF a (suc b)))) :
    Nonempty (Derivation body Delta (bounded a b)) := by
  obtain ⟨hd⟩ := InternalLeastNumberProof.actualRightSuccessorSplit body alpha a b
  rw [InternalSourceInversionSupportProof.onEquality] at hd
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (weakenClosed hd Delta) h⟩

theorem boundTrans (a b c : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (bounded a b)))
    (hbc : Nonempty (Derivation body Delta (bounded b c))) :
    Nonempty (Derivation body Delta (bounded a c)) :=
  fromWeak a c (InternalUnpairReverseBoundsArithmeticProof.weakTrans a b c
    (OrderProof.strictNext a b hab) (OrderProof.strictNext b c hbc))

theorem budgetStep (elapsed old remaining initial : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (ltF remaining old)))
    (hb : Nonempty (Derivation body Delta (bounded (add elapsed old) initial))) :
    Nonempty (Derivation body Delta (bounded (add (suc elapsed) remaining) initial)) := by
  obtain ⟨ha⟩ := addStrictLeft elapsed remaining old hd
  obtain ⟨hdisc⟩ := InternalBetaBoundaryProof.actualDiscreteOrderBoundary body alpha
    (add elapsed remaining) (add elapsed old)
  rw [InternalSourceInversionSupportProof.onEquality] at hdisc
  have hstep : Nonempty (Derivation body Delta
      (bounded (suc (add elapsed remaining)) (add elapsed old))) :=
    ⟨Derivation.implicationElimination (weakenClosed hdisc Delta) ha⟩
  have htransport := OrderProof.transport (suc (add elapsed remaining)) (add elapsed old)
    (add (suc elapsed) remaining) (add elapsed old)
    ⟨symm (leftSuccessor elapsed remaining)⟩ ⟨refl _⟩ hstep
  exact boundTrans (add (suc elapsed) remaining) (add elapsed old) initial htransport hb

theorem budgetZero (size remaining : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (bounded (add size remaining) size))) :
    Nonempty (Derivation body Delta (eqn remaining z)) := by
  apply zeroSuccessorCases Delta remaining
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro beta j Theta predecessor hj he
    simp only [eqnRelabel,zRelabel]
    have hb' := renameInto hb j Theta hj
    simp only [OrderProof.boundedRename,InternalOriginalOrderSyntaxProof.addRelabel] at hb'
    obtain ⟨he⟩ := he
    have hp : Nonempty (Derivation body Theta
        (ltF (size.relabel j) (add (size.relabel j) (suc predecessor)))) := by
      apply actualOriginalOrderIntroduction body beta Theta (size.relabel j)
        (add (size.relabel j) (suc predecessor)) predecessor
      rw [InternalSourceInversionSupportProof.onEquality]
      exact ⟨refl _⟩
    obtain ⟨hp⟩ := hp
    have hstrict := orderRight (size.relabel j) (congAddLeft (size.relabel j) (symm he)) hp
    exact InternalOriginalPairingOrderArithmeticProof.strictWeakConflict
      (size.relabel j) (add (size.relabel j) (remaining.relabel j)) _ ⟨hstrict⟩
      (OrderProof.strictNext (add (size.relabel j) (remaining.relabel j)) (size.relabel j) hb')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
