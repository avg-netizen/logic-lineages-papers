module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInsertionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (symm trans)
open InternalAdditionLawsProof (add associativity congAddLeft)
open InternalAdditionCancellationProof (commutativity)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalOrderSyntaxProof (ltF)
open OriginalNumericListSort OriginalNumericListSortInsertionProof
open SortWeightedDefinitions SortWeightedSortInductionDefinitions SortWeightedSortInductionBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {k : Nat} (F : Program (k+1))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (sorted sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields F z sorted sum params))) :
 Nonempty (Derivation body Delta (result F sorted sum params)) := by
 have he := valueUnique sort z sorted ![z] OriginalNumericListSortValueProof.sortNil (andLeft hf)
 exact headTransport (weighted F) sum z sorted params he (andRight hf)

theorem consCore (raw head tail sorted sum st hw ts : OTerm alpha)
 (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw sorted sum params)))
 (hst : Nonempty (Derivation body Delta (graph1 sort st tail)))
 (hh : Nonempty (Derivation body Delta (programGraph F hw (Fin.cons head params))))
 (ht : Nonempty (Derivation body Delta (programGraph (weighted F) ts (Fin.cons tail params)))) :
 Nonempty (Derivation body Delta (result F sorted sum params)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hsw := belowRawApply F raw tail st ts params hi hb (andIntro hst ht)
 have hins := OriginalNumericListSortAdjacentSupportProof.sortConsRecover raw head tail st sorted hc hst (andLeft hf)
 have hout := SortWeightedInsertionProof.actualInsertion k F body alpha Delta st head sorted hw ts params hins hh hsw
 obtain ⟨he⟩ := SortWeightedFoldProof.consUnique F raw head tail hw ts sum params hc hh ht (andRight hf)
 exact outputTransport (weighted F) (add hw ts) sum (Fin.cons sorted params) ⟨symm he⟩ hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortCore
