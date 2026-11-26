module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeySameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalActiveClassKernelEqualityProof
open EvaluatorKeyPut EvaluatorKeyRelationProof EvaluatorKeySameProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
theorem actualHit : EvaluatorKeyPutTargets.ActualHit := by
 intro p H G W P body alpha Delta seed candidate parameter hd hr
 have hm := fromRelation p H G W P seed candidate parameter hd hr
 exact andIntro (andLeft hm) (fromKey p H G W seed candidate parameter (andRight hm))
theorem actualRows : EvaluatorKeyPutTargets.ActualRows := by
 intro p H G W P body alpha Delta left right candidate parameter hl hr hs
 let A := graph3 (relationTest p H G W P) (numeral 1) left candidate parameter
 let B := graph3 (relationTest p H G W P) (numeral 1) right candidate parameter
 have hk := toKey p H G W left right parameter hs
 have hf : Nonempty (Derivation body (A :: Delta) B) := by
   have hm := fromRelation p H G W P left candidate parameter (withHyp hl A)
     (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact toRelation p H G W P right candidate parameter (withHyp hr A)
     (andIntro (andLeft hm) (keyRowForward (evaluatorKey p H G W) left right candidate parameter
       (withHyp hk A) (andRight hm)))
 have hb : Nonempty (Derivation body (B :: Delta) A) := by
   have hm := fromRelation p H G W P right candidate parameter (withHyp hr B)
     (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   exact toRelation p H G W P left candidate parameter (withHyp hl B)
     (andIntro (andLeft hm) (keyRowBackward (evaluatorKey p H G W) left right candidate parameter
       (withHyp hk B) (andRight hm)))
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
   (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutInternalProof
