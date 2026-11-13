module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalRawListRecursionSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalAdditionLawsProof (add)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalOrderSyntaxProof (ltF)
open OriginalNumericListSort
open SortWeightedDefinitions SortWeightedInductionDefinitions SortWeightedInductionSyntax
open SortWeightedInsertionCore
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {k : Nat} (F : Program (k+1))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem fieldsRename {beta : Type} (raw x inserted weight sum : OTerm alpha)
 (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (fields F raw x inserted weight sum params).relabel j =
 fields F (raw.relabel j) (x.relabel j) (inserted.relabel j) (weight.relabel j)
   (sum.relabel j) (fun i => (params i).relabel j) := by
 simp only [fields,conjunctionRename,graph2,programRename,consTermRename,emptyRename]

@[simp] theorem resultRename {beta : Type} (inserted weight sum : OTerm alpha)
 (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (result F inserted weight sum params).relabel j =
 result F (inserted.relabel j) (weight.relabel j) (sum.relabel j)
   (fun i => (params i).relabel j) := by
 simp only [result,programRename,InternalOriginalOrderSyntaxProof.addRelabel,consTermRename]

theorem afterAt2 (raw head tail x inserted weight sum ti hw : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 (hh : Nonempty (Derivation body Delta (programGraph F hw (Fin.cons head params))))
 : Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 apply programCases (weighted F) (Fin.cons tail params) _
 intro beta j Theta ts hj ht
 rw [resultRename]
 simp only [consTermRename,emptyRename] at ht
 have hi' := renameInto hi j Theta hj
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename] at hf'
 have hlt' := renameInto hlt j Theta hj
 simp only [InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 have hti' := renameInto hti j Theta hj
 simp only [graph2Rename] at hti'
 have hh' := renameInto hh j Theta hj
 simp only [programRename,consTermRename] at hh'
 exact afterCore F (raw.relabel j) (head.relabel j) (tail.relabel j) (x.relabel j) (inserted.relabel j) (weight.relabel j) (sum.relabel j) (ti.relabel j) (hw.relabel j) ts (fun i => (params i).relabel j) hi' hc' hf' hlt' hti' hh' ht

theorem afterAt1 (raw head tail x inserted weight sum ti : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 (hti : Nonempty (Derivation body Delta (graph2 insert ti tail x)))
 : Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 apply programCases F (Fin.cons head params) _
 intro beta j Theta hw hj hh
 rw [resultRename]
 simp only [consTermRename,emptyRename] at hh
 have hi' := renameInto hi j Theta hj
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename] at hf'
 have hlt' := renameInto hlt j Theta hj
 simp only [InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 have hti' := renameInto hti j Theta hj
 simp only [graph2Rename] at hti'
 exact afterAt2 F (raw.relabel j) (head.relabel j) (tail.relabel j) (x.relabel j) (inserted.relabel j) (weight.relabel j) (sum.relabel j) (ti.relabel j) hw (fun i => (params i).relabel j) hi' hc' hf' hlt' hti' hh

theorem afterAt0 (raw head tail x inserted weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw x inserted weight sum params)))
 (hlt : Nonempty (Derivation body Delta (ltF head x)))
 : Nonempty (Derivation body Delta (result F inserted weight sum params)) := by
 apply programCases insert ![tail,x] _
 intro beta j Theta ti hj hti
 rw [resultRename]
 simp only [consTermRename,emptyRename] at hti
 have hi' := renameInto hi j Theta hj
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename] at hf'
 have hlt' := renameInto hlt j Theta hj
 simp only [InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 exact afterAt1 F (raw.relabel j) (head.relabel j) (tail.relabel j) (x.relabel j) (inserted.relabel j) (weight.relabel j) (sum.relabel j) ti (fun i => (params i).relabel j) hi' hc' hf' hlt' hti

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedInsertionQueries
