module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAbsorptionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionClosureLogicProof (closedApply)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename)
open OriginalNumericListSort
open OriginalNumericListSortAdjacentSupportProof (sortConsRecover)
open OriginalNumericListSortIdempotenceDefinitions OriginalNumericListSortIdempotenceSyntaxProof OriginalNumericListSortIdempotenceBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (sorted again : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z sorted again))) :
 Nonempty (Derivation body Delta (equal again sorted)) := by
 have he := valueUnique sort sorted z ![z] (andLeft hf) OriginalNumericListSortValueProof.sortNil
 have ha := headTransport sort again sorted z Fin.elim0 he (andRight hf)
 simpa only [equalEqn] using valueUnique sort again sorted ![z] ha (andLeft hf)

theorem consValues (raw head tail sorted again ts ta : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw sorted again)))
 (hts : Nonempty (Derivation body Delta (graph1 sort ts tail)))
 (hta : Nonempty (Derivation body Delta (graph1 sort ta ts))) :
 Nonempty (Derivation body Delta (equal again sorted)) := by
 have hb := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have he := belowRawApply raw tail ts ta hi hb (andIntro hts hta)
 have heq : Nonempty (Derivation body Delta (eqn ta ts)) := by simpa only [equalEqn] using he
 have hfixed := outputTransport sort ta ts ![ts] heq hta
 have hinsert := sortConsRecover raw head tail ts sorted hc hts (andLeft hf)
 exact closedApply (OriginalNumericListSortAbsorptionProof.absorption body alpha ts head sorted ts again sorted)
   (andIntro hinsert (andIntro hfixed (andIntro (andRight hf) hinsert)))

theorem consAtTail (raw head tail sorted again ts : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw sorted again)))
 (hts : Nonempty (Derivation body Delta (graph1 sort ts tail))) :
 Nonempty (Derivation body Delta (equal again sorted)) := by
 apply programCases sort ![ts] _
 intro beta rho Theta ta hrho hta
 rw [unaryVectorRename] at hta
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 have hts' := renameInto hts rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [fields,conjunctionRename,graph1Rename] at hf'
 simp only [graph1Rename] at hts'
 exact consValues (raw.relabel rho) (head.relabel rho) (tail.relabel rho)
   (sorted.relabel rho) (again.relabel rho) (ts.relabel rho) ta hi' hc' hf' hts' hta

theorem consCore (raw head tail sorted again : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields raw sorted again))) :
 Nonempty (Derivation body Delta (equal again sorted)) := by
 apply programCases sort ![tail] _
 intro beta rho Theta ts hrho hts
 rw [unaryVectorRename] at hts
 rw [equalRename]
 have hi' := renameInto hi rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 have hf' := renameInto hf rho Theta hrho
 simp only [belowRawRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [fields,conjunctionRename,graph1Rename] at hf'
 exact consAtTail (raw.relabel rho) (head.relabel rho) (tail.relabel rho)
   (sorted.relabel rho) (again.relabel rho) ts hi' hc' hf' hts
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortIdempotenceCoreProof
