module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortInsertionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionCore
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
open SortWeightedDefinitions SortWeightedInductionDefinitions SortWeightedInductionBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {k : Nat} (F : Program (k+1))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields F z x inserted weight sum params))) :
 Nonempty (Derivation body Delta (result F inserted weight sum params)) :=
 SortWeightedFoldProof.consValue F inserted x z weight sum params
   (nilRecover x inserted (andLeft hf)) (andLeft (andRight hf)) (andRight (andRight hf))

theorem beforeCore (raw head tail x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params)))
 (hlt : Nonempty (Derivation body Delta (ltF head x).not)) :
 Nonempty (Derivation body Delta (result F inserted weight sum params)) :=
 SortWeightedFoldProof.consValue F inserted x raw weight sum params
   (beforeRecover raw head tail x inserted hc (andLeft hf) hlt)
   (andLeft (andRight hf)) (andRight (andRight hf))

theorem afterCore (raw head tail x inserted weight sum ti hw ts : OTerm alpha)
 (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 (hh : Nonempty (Derivation body Delta (programGraph F hw (Fin.cons head params))))
 (ht : Nonempty (Derivation body Delta (programGraph (weighted F) ts (Fin.cons tail params)))) :
 Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have htiw := belowRawApply F raw tail x ti weight ts params hi hb
   (andIntro hti (andIntro (andLeft (andRight hf)) ht))
 have hcons := afterRecover raw head tail x ti inserted hc hti (andLeft hf) hlt
 have hvalue := SortWeightedFoldProof.consValue F inserted head ti hw (add weight ts) params hcons hh htiw
 obtain ⟨hsum⟩ := SortWeightedFoldProof.consUnique F raw head tail hw ts sum params hc hh ht
   (andRight (andRight hf))
 have he : Derivation body Delta (eqn (add hw (add weight ts)) (add weight sum)) :=
   trans (commutativity hw (add weight ts))
     (trans (associativity weight ts hw)
       (trans (congAddLeft weight (commutativity ts hw))
         (congAddLeft weight (symm hsum))))
 exact outputTransport (weighted F) (add hw (add weight ts)) (add weight sum)
   (Fin.cons inserted params) ⟨he⟩ hvalue
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionCore
