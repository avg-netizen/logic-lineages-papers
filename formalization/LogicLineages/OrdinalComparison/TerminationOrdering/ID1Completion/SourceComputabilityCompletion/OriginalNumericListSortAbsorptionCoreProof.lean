module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortCommutationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionClosureLogicProof (closedApply)
open InternalOriginalOrderSyntaxProof (ltF)
open OriginalNumericListSort OriginalNumericListSortInsertionProof
open OriginalNumericListSortAdjacentSupportProof (sortConsRecover)
open OriginalNumericListSortAbsorptionDefinitions OriginalNumericListSortAbsorptionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (x inserted sorted left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z x inserted sorted left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hc := nilRecover x inserted (andLeft hf)
 have hl := sortConsRecover inserted x z sorted left hc (andLeft (andRight hf)) (andLeft (andRight (andRight hf)))
 simpa only [equalEqn] using valueUnique insert left right ![sorted,x] hl (andRight (andRight (andRight hf)))

theorem beforeCore (raw head tail x inserted sorted left right : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
 (hlt : Nonempty (Derivation body Delta (ltF head x).not)) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hcons := beforeRecover raw head tail x inserted hc (andLeft hf) hlt
 have hr := OriginalNumericListSortValueProof.sortCons inserted x raw sorted right hcons
   (andLeft (andRight hf)) (andRight (andRight (andRight hf)))
 simpa only [equalEqn] using valueUnique sort left right ![inserted] (andLeft (andRight (andRight hf))) hr

theorem afterCore (raw head tail x inserted sorted left right ti ts tl tr : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw x inserted sorted left right)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 (hts : Nonempty (Derivation body Delta (graph1 sort ts tail)))
 (htl : Nonempty (Derivation body Delta (graph1 sort tl ti)))
 (htr : Nonempty (Derivation body Delta (graph2 insert tr ts x))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have he := belowRawApply raw tail x ti ts tl tr hi hb (andIntro hti (andIntro hts (andIntro htl htr)))
 have hcons := afterRecover raw head tail x ti inserted hc hti (andLeft hf) hlt
 have hl := sortConsRecover inserted head ti tl left hcons htl (andLeft (andRight (andRight hf)))
 have hs := sortConsRecover raw head tail ts sorted hc hts (andLeft (andRight hf))
 have heq : Nonempty (Derivation body Delta (eqn tl tr)) := by simpa only [equalEqn] using he
 have hl' := headTransport insert left tl tr ![head] heq hl
 exact closedApply (OriginalNumericListSortCommutationProof.insertCommutation body alpha ts x head tr sorted left right)
   (andIntro htr (andIntro hl' (andIntro hs (andRight (andRight (andRight hf))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionCoreProof
