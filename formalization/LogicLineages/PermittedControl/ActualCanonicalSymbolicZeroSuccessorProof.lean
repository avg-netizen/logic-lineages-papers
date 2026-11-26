module
public import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorTargets
import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorOrderedProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataProof
import LogicLineages.PermittedControl.ActualNormalizedTapeZeroTransitionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessor
open ActualZeroClassReplacement ActualCanonicalOperandGrouping ActualCanonicalNormalizedTape
open ActualWeightedReadNormalization ActualNormalizedTapeZeroTransition
open ActualFullValueLabels ActualFullValueMaximalMetadata ActualMixedRowLeadingAnnotations
open ActualMixedRowLeadingSum

theorem exactCanonicalSuccessorWitness : ExactCanonicalSuccessorWitness := by
  intro f B chosen ρ strict C r constant raw xs anns a live bound canonical
  dsimp only
  intro aligned paid active matching maximum zero ready transfer
  have cert := exactCanonicalTapeCertificate f ρ raw xs live canonical
  obtain ⟨old,legacy,_,_,_,_,_⟩ := (exactNormalizedReads f ρ raw).2 live
  obtain ⟨out,found,_,tapeEq,_,_⟩ := (exactCanonicalReads f ρ raw).2 old legacy
  have outputEq : out = xs := Option.some.inj (found.symm.trans canonical)
  have frames : xs.map Prod.fst = groupTyped (raw.map Prod.fst) := outputEq ▸ tapeEq
  have ownZero : maximalCoefficient (xs.map Prod.fst) a = 0 := by rw [frames]; exact zero
  obtain ⟨D,maxValue,_,coef,_⟩ := exactActualMaximalMetadata f B chosen ρ (xs.map Prod.fst)
    (xs.map Prod.snd) anns aligned paid active a matching
  have same : D = C := Option.some.inj (maxValue.symm.trans maximum)
  subst D
  have rowZero := coef.symm.trans ownZero
  have present : C ∈ fullValues f anns := (List.max?_eq_some_iff.mp maximum).1
  obtain ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,_live,_ranks,_inRange,
    _sameVal,_sameRow,replacement,_weakCount,_weakValue,_strictCharge,cleaned⟩ :=
    exactTapeZeroTransition f B chosen ρ strict C r constant raw xs anns
      bound cert aligned ready present rowZero transfer
  refine ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,replacement,cleaned,?_⟩
  rw [canonicalSuccessor,← frames]
  exact exactOrderedSuccessorErasure f B chosen ρ C constant xs anns a moved
    aligned paid active matching maximum ownZero moves

end LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessor
