module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallIndexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallRowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof (orderRight)
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof InternalRawListRecursionSupportProof
open InternalQuotientComparisonProof (orLeft orRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalHereditaryInternalExpansionSmallIndexProof
open OriginalContextInsertion OriginalContextInsertionLengthProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem knownBound (row count known index : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (lengthGraph count row)))
 (hk : Nonempty (Derivation body Delta (lengthGraph known row)))
 (hb : Nonempty (Derivation body Delta (Below index count))) :
 Nonempty (Derivation body Delta (ltF index known)) := by
 obtain ⟨he⟩ := valueUnique length count known (Fin.cons row Fin.elim0) hl hk
 obtain ⟨hb⟩ := hb
 exact ⟨orderRight index he hb⟩

theorem unaryLookup (row first index count value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph row first z)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count row)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index row))) :
 Nonempty (Derivation body Delta (eqn value first)) := by
 have hk := knownBound row count (suc z) index hl (lengthCons row first z z hc lengthZero) hb
 have hz := belowOneZero index hk
 have hv0 := headTransport InternalRawListRecursion.lookup value index z (Fin.cons row Fin.elim0) hz hv
 exact valueUnique InternalRawListRecursion.lookup value first (Fin.cons z (Fin.cons row Fin.elim0))
   hv0 (OriginalAllPositionContextDeleteBaseProof.lookupZero row first z hc)

theorem binaryLookup (row first tail second index count value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph row first tail)))
 (ht : Nonempty (Derivation body Delta (consGraph tail second z)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count row)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index row))) :
 Nonempty (Derivation body Delta (eqn value first ⊔ eqn value second)) := by
 have hk := knownBound row count (suc (suc z)) index hl
   (lengthCons row first tail (suc z) hc (lengthCons tail second z z ht lengthZero)) hb
 apply belowTwoCases index _ hk
 · intro Theta inc he
   have hv0 := headTransport InternalRawListRecursion.lookup value index z (Fin.cons row Fin.elim0)
     he (weakenProof hv inc)
   exact orLeft (valueUnique InternalRawListRecursion.lookup value first (Fin.cons z (Fin.cons row Fin.elim0))
     hv0 (OriginalAllPositionContextDeleteBaseProof.lookupZero row first tail (weakenProof hc inc)))
 · intro beta rho Theta hrho he
   simp only [disjunctionRename,eqnRename]
   have hv' := renameInto hv rho Theta hrho
   have hc' := renameInto hc rho Theta hrho
   have ht' := renameInto ht rho Theta hrho
   simp only [graph2Rename] at hv'
   simp only [consGraphRename,zRelabel] at hc' ht'
   have hv1 := headTransport InternalRawListRecursion.lookup (value.relabel rho) (index.relabel rho) (suc z)
     (Fin.cons (row.relabel rho) Fin.elim0) he hv'
   have hvalue := lookupValue (second.relabel rho) (suc z) (row.relabel rho) (tail.relabel rho)
     (OriginalAllPositionContextDeleteBaseProof.dropOne (row.relabel rho) (first.relabel rho) (tail.relabel rho) hc')
     (consHead (tail.relabel rho) (second.relabel rho) z ht')
   exact orRight (valueUnique InternalRawListRecursion.lookup (value.relabel rho) (second.relabel rho)
     (Fin.cons (suc z) (Fin.cons (row.relabel rho) Fin.elim0)) hv1 hvalue)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallRowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallRowProof
