module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClassProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumInternalReflexiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.WrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalEqualityTestCompositionProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem candidateTransport (Q : Program 3) (seed candidate parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn seed candidate)))
    (hh : Nonempty (Derivation body Delta (graph3 Q (suc z) seed seed parameter))) :
    Nonempty (Derivation body Delta (graph3 Q (suc z) seed candidate parameter)) := by
  apply graphInputTransport body alpha 3 Delta (OrdinaryArithmetic.graphFormula Q)
    (suc z) ![seed,seed,parameter] ![seed,candidate,parameter] _ hh
  intro i
  simp only [onEquality]
  exact Fin.cases (Nonempty.intro (refl seed))
    (Fin.cases he (Fin.cases (Nonempty.intro (refl parameter)) (fun j => Fin.elim0 j))) i

theorem compareCases (candidate seed : OTerm alpha) (goal : Formula alpha)
    (hl : Nonempty (Derivation body (ltF candidate seed :: Delta) goal))
    (he : Nonempty (Derivation body (eqn candidate seed :: Delta) goal))
    (hr : Nonempty (Derivation body (ltF seed candidate :: Delta) goal)) :
    Nonempty (Derivation body Delta goal) := by
  obtain ⟨cmp⟩ := actualOriginalComparison body alpha candidate seed
  have hc := compareView (weakenClosed cmp Delta)
  obtain ⟨hl⟩ := hl
  obtain ⟨he⟩ := he
  obtain ⟨hr⟩ := hr
  have rest : Derivation body Delta ((eqn candidate seed ⊔ ltF seed candidate).imp goal) :=
    Derivation.implicationIntroduction (disjunctionElimination
      (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction he) _)
      (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc (Derivation.implicationIntroduction hl) rest⟩

theorem rejectedEquivalence (T C P : Program 2) (E : Program 3)
    (seed candidate parameter : OTerm alpha)
    (hz : Nonempty (Derivation body Delta
      (graph2 InternalEqualityTest.equalityTest z candidate seed))) :
    (Nonempty (Derivation body Delta (graph3
      (OriginalTransparentMinimum.reflexiveClassTest T (kernel T C P E)) (suc z) seed candidate parameter)) ↔
     Nonempty (Derivation body Delta (graph3 (kernel T C P E) (suc z) seed candidate parameter))) := by
  let xs : Fin 3 → OTerm alpha := ![seed,candidate,parameter]
  let control : Program 3 := .composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0]
  let target : Program 3 := .composition T ![.projection 0,.projection 2]
  have hc := binaryValue InternalEqualityTest.equalityTest (.projection 1) (.projection 0)
    z candidate seed xs hz (projectionValue 1 xs) (projectionValue 0 xs)
  exact ⟨fun h => zeroBranchElim control (kernel T C P E) target (suc z) xs hc h,
    fun h => zeroBranchIntro control (kernel T C P E) target (suc z) xs hc h⟩

theorem equalHits (T C P : Program 2) (E : Program 3)
    (seed candidate parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 T (suc z) seed parameter)))
    (he : Nonempty (Derivation body Delta (eqn candidate seed))) :
    Nonempty (Derivation body Delta (graph3 (kernel T C P E) (suc z) seed candidate parameter)) ∧
    Nonempty (Derivation body Delta (graph3
      (OriginalTransparentMinimum.reflexiveClassTest T (kernel T C P E)) (suc z) seed candidate parameter)) := by
  obtain ⟨he⟩ := he
  have hraw := TransparentPrimary.InternalProof.internalClassReflexivity T C P E body alpha Delta
    seed parameter ht
  have hwrap := OriginalTransparentMinimumInternalReflexiveProof.actualOriginalTransparentMinimumInternalReflexive
    T (kernel T C P E) body alpha Delta seed parameter
  obtain ⟨hwrap⟩ := hwrap
  obtain ⟨ht⟩ := ht
  exact ⟨candidateTransport _ seed candidate parameter ⟨symm he⟩ hraw,
    candidateTransport _ seed candidate parameter ⟨symm he⟩
      ⟨Derivation.implicationElimination hwrap ht⟩⟩

theorem wrapperAcceptance : Targets.WrapperAcceptance := by
  intro T C P E body alpha Delta seed candidate parameter ht
  constructor
  · intro hw
    apply compareCases candidate seed _
    · exact (rejectedEquivalence T C P E seed candidate parameter
        (InternalEqualityTestProof.rejectForwardOrder candidate seed
          ⟨Derivation.hypothesis List.mem_cons_self⟩)).mp (withHyp hw _)
    · exact (equalHits T C P E seed candidate parameter (withHyp ht _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩).1
    · exact (rejectedEquivalence T C P E seed candidate parameter
        (InternalEqualityTestProof.rejectBackwardOrder candidate seed
          ⟨Derivation.hypothesis List.mem_cons_self⟩)).mp (withHyp hw _)
  · intro hp
    apply compareCases candidate seed _
    · exact (rejectedEquivalence T C P E seed candidate parameter
        (InternalEqualityTestProof.rejectForwardOrder candidate seed
          ⟨Derivation.hypothesis List.mem_cons_self⟩)).mpr (withHyp hp _)
    · exact (equalHits T C P E seed candidate parameter (withHyp ht _)
        ⟨Derivation.hypothesis List.mem_cons_self⟩).2
    · exact (rejectedEquivalence T C P E seed candidate parameter
        (InternalEqualityTestProof.rejectBackwardOrder candidate seed
          ⟨Derivation.hypothesis List.mem_cons_self⟩)).mpr (withHyp hp _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.WrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.WrapperProof
