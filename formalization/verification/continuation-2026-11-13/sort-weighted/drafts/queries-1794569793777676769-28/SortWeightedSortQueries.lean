module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortQueries
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
open SortWeightedDefinitions SortWeightedSortInductionDefinitions SortWeightedSortInductionSyntax
open SortWeightedSortCore
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {k : Nat} (F : Program (k+1))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem fieldsRename {beta : Type} (raw sorted sum : OTerm alpha)
 (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (fields F raw sorted sum params).relabel j =
 fields F (raw.relabel j) (sorted.relabel j) (sum.relabel j) (fun i => (params i).relabel j) := by
 simp only [fields,conjunctionRename,graph1,programRename,consTermRename,emptyRename]
@[simp] theorem resultRename {beta : Type} (sorted sum : OTerm alpha)
 (params : Fin k → OTerm alpha) (j : alpha → beta) :
 (result F sorted sum params).relabel j =
 result F (sorted.relabel j) (sum.relabel j) (fun i => (params i).relabel j) := by
 simp only [result,programRename,consTermRename]

theorem consAt2 (raw head tail sorted sum st hw : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw sorted sum params)))
 (hst : Nonempty (Derivation body Delta (graph1 sort st tail)))
 (hh : Nonempty (Derivation body Delta (programGraph F hw (Fin.cons head params))))
 : Nonempty (Derivation body Delta (result F sorted sum params)) := by
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
 have hst' := renameInto hst j Theta hj
 simp only [graph1Rename] at hst'
 have hh' := renameInto hh j Theta hj
 simp only [programRename,consTermRename] at hh'
 exact SortWeightedSortCore.consCore F (raw.relabel j) (head.relabel j) (tail.relabel j) (sorted.relabel j) (sum.relabel j) (st.relabel j) (hw.relabel j) ts (fun i => (params i).relabel j) hi' hc' hf' hst' hh' ht

theorem consAt1 (raw head tail sorted sum st : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw sorted sum params)))
 (hst : Nonempty (Derivation body Delta (graph1 sort st tail)))
 : Nonempty (Derivation body Delta (result F sorted sum params)) := by
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
 have hst' := renameInto hst j Theta hj
 simp only [graph1Rename] at hst'
 exact consAt2 F (raw.relabel j) (head.relabel j) (tail.relabel j) (sorted.relabel j) (sum.relabel j) (st.relabel j) hw (fun i => (params i).relabel j) hi' hc' hf' hst' hh

theorem consAt0 (raw head tail sorted sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw F raw params)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields F raw sorted sum params)))
 : Nonempty (Derivation body Delta (result F sorted sum params)) := by
 apply programCases sort ![tail] _
 intro beta j Theta st hj hst
 rw [resultRename]
 simp only [consTermRename,emptyRename] at hst
 have hi' := renameInto hi j Theta hj
 simp only [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 simp only [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename] at hf'
 exact consAt1 F (raw.relabel j) (head.relabel j) (tail.relabel j) (sorted.relabel j) (sum.relabel j) st (fun i => (params i).relabel j) hi' hc' hf' hst

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedSortQueries
