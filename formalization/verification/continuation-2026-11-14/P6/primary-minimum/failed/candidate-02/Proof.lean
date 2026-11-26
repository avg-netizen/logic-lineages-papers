module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.WrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨C,P,E,hs⟩ := TransparentPrimary.SelectionProof.supplierSelection n arity
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hL := TransparentPrimary.NativeProof.calibration n arity
    (OriginalTypedDecoder.target H G) C P E hT hs
  have hr := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (TransparentPrimary.primary (OriginalTypedDecoder.target H G) C P E) hp hH hG hW hL
  exact ⟨C,P,E,hs,hL,hr⟩

theorem actualMinimum : Targets.ActualMinimum := by
  intro T C P E body alpha Delta out seed parameter earlier
  let K := kernel T C P E
  let A := graph2 T (numeral 1) seed parameter ⊓
    graph2 (OriginalTransparentMinimum.minimum T K) out seed parameter
  have ha : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  have ht := Derivation.conjunctionLeft ha
  obtain ⟨hm⟩ := OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalMinimum
    T K body alpha (A :: Delta) out seed parameter earlier
  have hm := Derivation.implicationElimination hm ha
  have hb := Derivation.conjunctionLeft hm
  have hh := Derivation.conjunctionLeft (Derivation.conjunctionRight hm)
  have hn := Derivation.conjunctionRight (Derivation.conjunctionRight hm)
  obtain ⟨hh'⟩ := (WrapperProof.wrapperAcceptance T C P E body alpha (A :: Delta)
    seed out parameter ⟨ht⟩).mp ⟨hh⟩
  let B := InternalLessThan.strictLess earlier out
  let F := graph3 K (numeral 1) seed earlier parameter
  have hmiss : Derivation body (F :: B :: A :: Delta)
      (graph3 (OriginalTransparentMinimum.reflexiveClassTest T K) (numeral 1) seed earlier parameter).not := by
    obtain ⟨hn⟩ := withHyp (withHyp (Nonempty.intro hn) B) F
    exact Derivation.implicationElimination hn
      (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  have hactual : Nonempty (Derivation body (F :: B :: A :: Delta) F) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htarget := withHyp (withHyp (Nonempty.intro ht) B) F
  obtain ⟨hwrapped⟩ := (WrapperProof.wrapperAcceptance T C P E body alpha
    (F :: B :: A :: Delta) seed earlier parameter htarget).mpr hactual
  have hfalse := Derivation.implicationElimination hmiss hwrapped
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction hb (Derivation.conjunctionIntroduction hh'
      (Derivation.implicationIntroduction (Derivation.implicationIntroduction hfalse))))⟩

theorem guardedActualClass : Targets.GuardedActualClass := by
  intro p H G W C P E body alpha Delta out seed parameter
  let T := OriginalTypedDecoder.target H G
  let K := kernel T C P E
  let guarded := OriginalTransparentMinimum.transparentInputs H G W K p
  let A := graph2 T (numeral 1) seed parameter ⊓
    graph2 guarded.base.oldRepresentative out seed parameter
  have ha : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hg⟩ := OriginalTransparentMinimumGlobalProof.actualOriginalTransparentMinimumInternalGuardedClass
    p H G W K body alpha (A :: Delta) out seed parameter
  have hw := Derivation.implicationElimination hg ha
  obtain ⟨h⟩ := (WrapperProof.wrapperAcceptance T C P E body alpha (A :: Delta)
    seed out parameter ⟨Derivation.conjunctionLeft ha⟩).mp ⟨hw⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMinimum.Proof
