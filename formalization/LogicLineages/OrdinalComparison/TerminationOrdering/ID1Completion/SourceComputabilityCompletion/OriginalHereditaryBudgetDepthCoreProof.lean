module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallIndexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalPairingOrderArithmeticProof (weakTransport)
open InternalQuotientComparisonProof (equalToNext)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalHereditaryBudgetDepthSyntaxProof
open OriginalHereditaryFuelProgram (budget)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalMultiplicationLawsProof (mul)
open InternalPairingSumBoundsArithmeticProof (successorWeak)
open OriginalContextInsertionBelowCoreProof (successorStrict)

theorem zeroCore (b c v w : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z b c v w))) :
 Nonempty (Derivation body Delta (result v w)) := by
 have hb := OriginalHereditaryInternalExpansionSmallIndexProof.belowOneZero b (andLeft hf)
 have hv0 := headTransport budget v b z (Fin.cons c Fin.elim0) hb (andLeft (andRight hf))
 have hv := valueUnique budget v (suc z) (Fin.cons z (Fin.cons c Fin.elim0))
   hv0 (OriginalHereditaryBudgetInternalProof.actualZero body alpha Delta c)
 have hw := valueUnique budget w (suc z) (Fin.cons z (Fin.cons c Fin.elim0))
   (andRight (andRight hf)) (OriginalHereditaryBudgetInternalProof.actualZero body alpha Delta c)
 exact weakTransport v w (suc z) (suc z) hv hw ⟨equalToNext (InternalTagArithmeticSupportProof.refl (suc z))⟩

theorem zeroLower (depth c v w previous : OTerm alpha)
 (hv : Nonempty (Derivation body Delta (graph2 budget v z c)))
 (hp : Nonempty (Derivation body Delta (graph2 budget previous depth c)))
 (hw : Nonempty (Derivation body Delta (graph2 budget w (suc depth) c))) :
 Nonempty (Derivation body Delta (result v w)) := by
 have he := valueUnique budget v (suc z) (Fin.cons z (Fin.cons c Fin.elim0)) hv
   (OriginalHereditaryBudgetInternalProof.actualZero body alpha Delta c)
 have hf := OriginalHereditaryBudgetInternalProof.actualSuccessorEquation body alpha Delta depth c previous w hp hw
 have hz : Nonempty (Derivation body Delta (ltF z (suc (mul c previous)))) := by
   obtain ⟨h⟩ := InternalUnpairArithmeticProof.leftWeakAdd (body := body) (Gamma := Delta) z (mul c previous)
   exact ⟨orderRight z (congSuc (InternalAdditionLawsProof.leftZero (mul c previous))) h⟩
 exact weakTransport _ _ _ _ he hf (successorWeak z (mul c previous) hz)

theorem atSuccessors (depth lower c v w p q : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row depth)))
 (hb : Nonempty (Derivation body Delta (ltF (suc lower) (suc (suc depth)))))
 (hp : Nonempty (Derivation body Delta (graph2 budget p lower c)))
 (hq : Nonempty (Derivation body Delta (graph2 budget q depth c)))
 (hv : Nonempty (Derivation body Delta (graph2 budget v (suc lower) c)))
 (hw : Nonempty (Derivation body Delta (graph2 budget w (suc depth) c))) :
 Nonempty (Derivation body Delta (result v w)) := by
 have hprevious := rowApply depth lower c p q hi (andIntro (successorStrict lower (suc depth) hb) (andIntro hp hq))
 have he := OriginalHereditaryBudgetInternalProof.actualSuccessorEquation body alpha Delta lower c p v hp hv
 have hf := OriginalHereditaryBudgetInternalProof.actualSuccessorEquation body alpha Delta depth c q w hq hw
 exact weakTransport _ _ _ _ he hf (OriginalHereditaryBudgetOrderArithmeticProof.stepWeak c c p q
   ⟨equalToNext (InternalTagArithmeticSupportProof.refl c)⟩ hprevious)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthCoreProof
