module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDataProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnSupplierProof
/-- CPS wrapper for actual internal witnesses; never an endpoint assumption. -/
def Consumer (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha))
 (children deletions produced : OTerm alpha) (psi : Formula alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (first second row : OTerm beta),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Supplier body Theta (children.relabel j) (deletions.relabel j) (produced.relabel j) first second row →
 Nonempty (Derivation body Theta (psi.relabel j))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consumerRename {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (children deletions produced : OTerm alpha) (psi : Formula alpha)
 (hi : ∀ f ∈ Delta, f.relabel j ∈ Theta)
 (next : Consumer body Delta children deletions produced psi) :
 Consumer body Theta (children.relabel j) (deletions.relabel j) (produced.relabel j) (psi.relabel j) := by
 intro gamma k Xi first second row hk hs
 have inc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hk _ (hi f hf)
 have hs' : Supplier body Xi (children.relabel (k ∘ j)) (deletions.relabel (k ∘ j))
   (produced.relabel (k ∘ j)) first second row := by simpa only [Term.relabel_relabel] using hs
 simpa only [formulaRelabelComposition] using next gamma (k ∘ j) Xi first second row inc hs'
theorem zeroWithRow (deletions produced front childRow : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add z deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (next : Consumer body Delta z deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases OriginalTypedArgumentObservations.reverse (Fin.cons front Fin.elim0) _
 intro beta j Theta row hi hq
 simp only [consTermRename,emptyRename,sucRelabel] at hq
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename,zRelabel,sucRelabel] at hl' hf' hp'
 have hs := UniformReturnDataProof.zero (deletions.relabel j) (produced.relabel j) (front.relabel j) (childRow.relabel j) row
   hl' hf' hp' hq
 exact next beta j Theta z z row hi (by simpa only [zRelabel,sucRelabel] using hs)
theorem zeroCases (deletions produced : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add z deletions) produced)))
 (next : Consumer body Delta z deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply UniformReturnPartitionProof.partitionCases z deletions produced psi hl
 intro beta j Theta front childRow hi hf hchild hp
 have hl' := renameInto hl j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,zRelabel,sucRelabel] at hl'
 apply zeroWithRow (deletions.relabel j) (produced.relabel j) front childRow (psi.relabel j) hl' hf hp
 simpa only [zRelabel,sucRelabel] using consumerRename j Theta z deletions produced psi hi next
theorem oneWithFirst (deletions produced front childRow row : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc z) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hrow : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 (next : Consumer body Delta (suc z) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases InternalRawListRecursion.lookup (Fin.cons deletions (Fin.cons produced Fin.elim0)) _
 intro beta j Theta first hi hq
 simp only [consTermRename,emptyRename,sucRelabel] at hq
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 have hrow' := renameInto hrow j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename,zRelabel,sucRelabel] at hl' hf' hp' hrow'
 have hs := UniformReturnDataProof.one (deletions.relabel j) (produced.relabel j) (front.relabel j) (childRow.relabel j) (row.relabel j) first
   hl' hf' hp' hrow' hq
 exact next beta j Theta first z (row.relabel j) hi (by simpa only [zRelabel,sucRelabel] using hs)
theorem oneWithRow (deletions produced front childRow : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc z) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (next : Consumer body Delta (suc z) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases OriginalTypedArgumentObservations.reverse (Fin.cons front Fin.elim0) _
 intro beta j Theta row hi hq
 simp only [consTermRename,emptyRename,sucRelabel] at hq
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename,zRelabel,sucRelabel] at hl' hf' hp'
 apply oneWithFirst (deletions.relabel j) (produced.relabel j) (front.relabel j) (childRow.relabel j) row (psi.relabel j)
   hl' hf' hp' hq
 simpa only [zRelabel,sucRelabel] using consumerRename j Theta (suc z) deletions produced psi hi next
theorem oneCases (deletions produced : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc z) deletions) produced)))
 (next : Consumer body Delta (suc z) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply UniformReturnPartitionProof.partitionCases (suc z) deletions produced psi hl
 intro beta j Theta front childRow hi hf hchild hp
 have hl' := renameInto hl j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,zRelabel,sucRelabel] at hl'
 apply oneWithRow (deletions.relabel j) (produced.relabel j) front childRow (psi.relabel j) hl' hf hp
 simpa only [zRelabel,sucRelabel] using consumerRename j Theta (suc z) deletions produced psi hi next
theorem twoWithSecond (deletions produced front childRow row first : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc (suc z)) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hrow : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (suc deletions) produced)))
 (next : Consumer body Delta (suc (suc z)) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases InternalRawListRecursion.lookup (Fin.cons deletions (Fin.cons produced Fin.elim0)) _
 intro beta j Theta second hi hq
 simp only [consTermRename,emptyRename,sucRelabel] at hq
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 have hrow' := renameInto hrow j Theta hi
 have hfirst' := renameInto hfirst j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename,zRelabel,sucRelabel] at hl' hf' hp' hrow' hfirst'
 have hs := UniformReturnDataProof.two (deletions.relabel j) (produced.relabel j) (front.relabel j) (childRow.relabel j) (row.relabel j) (first.relabel j) second
   hl' hf' hp' hrow' hfirst' hq
 exact next beta j Theta (first.relabel j) second (row.relabel j) hi (by simpa only [zRelabel,sucRelabel] using hs)
theorem twoWithFirst (deletions produced front childRow row : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc (suc z)) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hrow : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 (next : Consumer body Delta (suc (suc z)) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases InternalRawListRecursion.lookup (Fin.cons (suc deletions) (Fin.cons produced Fin.elim0)) _
 intro beta j Theta first hi hq
 simp only [consTermRename,emptyRename,sucRelabel] at hq
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 have hrow' := renameInto hrow j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename,zRelabel,sucRelabel] at hl' hf' hp' hrow'
 apply twoWithSecond (deletions.relabel j) (produced.relabel j) (front.relabel j) (childRow.relabel j) (row.relabel j) first (psi.relabel j)
   hl' hf' hp' hrow' hq
 simpa only [zRelabel,sucRelabel] using consumerRename j Theta (suc (suc z)) deletions produced psi hi next
theorem twoWithRow (deletions produced front childRow : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc (suc z)) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (next : Consumer body Delta (suc (suc z)) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases OriginalTypedArgumentObservations.reverse (Fin.cons front Fin.elim0) _
 intro beta j Theta row hi hq
 simp only [consTermRename,emptyRename,sucRelabel] at hq
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename,zRelabel,sucRelabel] at hl' hf' hp'
 apply twoWithFirst (deletions.relabel j) (produced.relabel j) (front.relabel j) (childRow.relabel j) row (psi.relabel j)
   hl' hf' hp' hq
 simpa only [zRelabel,sucRelabel] using consumerRename j Theta (suc (suc z)) deletions produced psi hi next
theorem twoCases (deletions produced : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc (suc z)) deletions) produced)))
 (next : Consumer body Delta (suc (suc z)) deletions produced psi) :
 Nonempty (Derivation body Delta psi) := by
 apply UniformReturnPartitionProof.partitionCases (suc (suc z)) deletions produced psi hl
 intro beta j Theta front childRow hi hf hchild hp
 have hl' := renameInto hl j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,zRelabel,sucRelabel] at hl'
 apply twoWithRow (deletions.relabel j) (produced.relabel j) front childRow (psi.relabel j) hl' hf hp
 simpa only [zRelabel,sucRelabel] using consumerRename j Theta (suc (suc z)) deletions produced psi hi next
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierQueries
