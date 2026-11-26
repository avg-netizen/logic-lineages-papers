module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open CompareDefinitions.Compare CompareSyntaxProof CompareBindingProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalListCodecDecompositionSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem resultTransport (raw left right a b x y candidate : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (eqn a x)))
    (hb : Nonempty (Derivation body Delta (eqn b y)))
    (h : Nonempty (Derivation body Delta (result raw left right a b candidate))) :
    Nonempty (Derivation body Delta (result raw left right x y candidate)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hw⟩ := OrderProof.transport b a y x hb ha ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  let N := newness raw left right candidate
  have hs : Derivation body (N :: Delta) (ltF b a) :=
    Derivation.implicationElimination (addHyp (Derivation.conjunctionRight h) N)
      (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.conjunctionIntroduction hw (Derivation.implicationIntroduction
    (orderRight y (addHyp ha N) (orderLeft a (addHyp hb N) hs)))⟩

theorem leftHitTail (raw head tail left right candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (suc z) left head)))
    (hn : Nonempty (Derivation body Delta (newness raw left right candidate))) :
    Nonempty (Derivation body Delta (newness tail left right candidate)) := by
  obtain ⟨hn⟩ := hn
  let A := equal head candidate
  have he : Nonempty (Derivation body Delta A.not) := by
    have heq : Nonempty (Derivation body (A :: Delta) (equal head candidate)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [equalEqn] at heq
    obtain ⟨heq⟩ := heq
    obtain ⟨hm⟩ := PrimaryCarrierBound.RunProof.poolMember left head candidate (withHyp hh A) ⟨symm heq⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionLeft (Derivation.conjunctionRight hn)) A) hm)⟩
  obtain ⟨hm⟩ := PrimaryMembership.Proof.missRecover raw head tail candidate (suc z) hc he
    ⟨Derivation.conjunctionLeft hn⟩
  exact ⟨Derivation.conjunctionIntroduction hm (Derivation.conjunctionRight hn)⟩

theorem rightMissTail (raw head tail left right candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (suc z) right head).not))
    (hn : Nonempty (Derivation body Delta (newness raw left right candidate))) :
    Nonempty (Derivation body Delta (newness tail left right candidate)) := by
  obtain ⟨hn⟩ := hn
  let A := equal head candidate
  have he : Nonempty (Derivation body Delta A.not) := by
    have heq : Nonempty (Derivation body (A :: Delta) (equal head candidate)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [equalEqn] at heq
    obtain ⟨hm⟩ := PrimaryCarrierBound.RunProof.poolMember right candidate head
      ⟨addHyp (Derivation.conjunctionRight (Derivation.conjunctionRight hn)) A⟩ heq
    obtain ⟨hh'⟩ := withHyp hh A
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hh' hm)⟩
  obtain ⟨hm⟩ := PrimaryMembership.Proof.missRecover raw head tail candidate (suc z) hc he
    ⟨Derivation.conjunctionLeft hn⟩
  exact ⟨Derivation.conjunctionIntroduction hm (Derivation.conjunctionRight hn)⟩

theorem hitResult (raw head tail left right a b candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (suc z) left head)))
    (h : Nonempty (Derivation body Delta (result tail left right a b candidate))) :
    Nonempty (Derivation body Delta (result raw left right a b candidate)) := by
  obtain ⟨h⟩ := h
  let N := newness raw left right candidate
  obtain ⟨ht⟩ := leftHitTail raw head tail left right candidate (withHyp hc N) (withHyp hh N)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (addHyp (Derivation.conjunctionRight h) N) ht))⟩

theorem missResult (raw head tail left right a b candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 contains (suc z) right head).not))
    (h : Nonempty (Derivation body Delta (result tail left right a b candidate))) :
    Nonempty (Derivation body Delta (result raw left right (suc a) (suc b) candidate)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hw⟩ := OrderProof.successor b a ⟨Derivation.conjunctionLeft h⟩
  let N := newness raw left right candidate
  obtain ⟨ht⟩ := rightMissTail raw head tail left right candidate (withHyp hc N) (withHyp hh N)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hs⟩ := OrderProof.strictSucc b a
    ⟨Derivation.implicationElimination (addHyp (Derivation.conjunctionRight h) N) ht⟩
  exact ⟨Derivation.conjunctionIntroduction hw (Derivation.implicationIntroduction hs)⟩

theorem newResult (raw left right a b candidate : OTerm alpha)
    (h : Nonempty (Derivation body Delta (bounded b a))) :
    Nonempty (Derivation body Delta (result raw left right (suc a) b candidate)) := by
  obtain ⟨hs⟩ := OrderProof.strictNext b a h
  exact ⟨Derivation.conjunctionIntroduction (orLeft hs)
    (Derivation.implicationIntroduction (addHyp hs _))⟩

theorem consKnown (raw head tail left right leftCount rightCount candidate a b : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included left right)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right)))
    (ha : Nonempty (Derivation body Delta (graph2 count a tail left)))
    (hb : Nonempty (Derivation body Delta (graph2 count b tail right))) :
    Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) := by
  have ih := belowRawApply raw tail left right a b candidate hrow (consTailDescent raw head tail hc)
    (andIntro hi (andIntro ha hb))
  let A := graph2 contains (suc z) left head
  let B := graph2 contains (suc z) right head
  apply formulaCases A
  · have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hB := PrimaryMonotonicity.InclusionProof.eliminate left right head (withHyp hi A) hA
    obtain ⟨el⟩ := StepProof.consHitEquation raw head tail left leftCount a
      (withHyp hc A) (withHyp ha A) (withHyp hl A) hA
    obtain ⟨er⟩ := StepProof.consHitEquation raw head tail right rightCount b
      (withHyp hc A) (withHyp hb A) (withHyp hr A) hB
    exact resultTransport raw left right a b leftCount rightCount candidate ⟨symm el⟩ ⟨symm er⟩
      (hitResult raw head tail left right a b candidate (withHyp hc A) hA (withHyp ih A))
  · have hA : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlEq := StepProof.consMissEquation raw head tail left leftCount a
      (withHyp hc A.not) (withHyp ha A.not) (withHyp hl A.not) hA
    apply formulaCases B
    · obtain ⟨el⟩ := withHyp hlEq B
      obtain ⟨er⟩ := StepProof.consHitEquation raw head tail right rightCount b
        (withHyp (withHyp hc A.not) B) (withHyp (withHyp hb A.not) B)
        (withHyp (withHyp hr A.not) B) ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨ih'⟩ := withHyp (withHyp ih A.not) B
      exact resultTransport raw left right (suc a) b leftCount rightCount candidate ⟨symm el⟩ ⟨symm er⟩
        (newResult raw left right a b candidate ⟨Derivation.conjunctionLeft ih'⟩)
    · obtain ⟨el⟩ := withHyp hlEq B.not
      have hB : Nonempty (Derivation body (B.not :: A.not :: Delta) B.not) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨er⟩ := StepProof.consMissEquation raw head tail right rightCount b
        (withHyp (withHyp hc A.not) B.not) (withHyp (withHyp hb A.not) B.not)
        (withHyp (withHyp hr A.not) B.not) hB
      exact resultTransport raw left right (suc a) (suc b) leftCount rightCount candidate ⟨symm el⟩ ⟨symm er⟩
        (missResult raw head tail left right a b candidate (withHyp (withHyp hc A.not) B.not)
          hB (withHyp (withHyp ih A.not) B.not))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareStepProof
