module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDataProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (trans congSuc)
open InternalAdditionLawsProof (add leftSuccessor leftZero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnSupplierProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zero (deletions produced front childRow row : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add z deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 : Supplier body Delta z deletions produced z z row := by
 apply fromData z deletions produced front childRow z z row hl hf hp hr
 intro beta j Theta old results hi ha
 simpa only [zRelabel] using OriginalResultStackZeroSlotsProof.actualZero body beta Theta (deletions.relabel j) results
theorem one (deletions produced front childRow row first : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc z) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first deletions produced)))
 : Supplier body Delta (suc z) deletions produced first z row := by
 apply fromData (suc z) deletions produced front childRow first z row hl hf hp hr
 intro beta j Theta old results hi ha
 have hl' := renameInto hl j Theta hi
 have hfirst' := renameInto hfirst j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph2Rename,sucRelabel,zRelabel] at hl' hfirst' ⊢
 have hlen := outputTransport OriginalContextInsertion.length
   (add (suc z) (deletions.relabel j)) (suc (deletions.relabel j))
   (Fin.cons (produced.relabel j) Fin.elim0) ⟨trans (leftSuccessor z (deletions.relabel j)) (congSuc (leftZero (deletions.relabel j)))⟩ hl'
 exact UniformReturnSlotsProof.oneChild
   (deletions.relabel j) (produced.relabel j) old results (first.relabel j) hlen ha hfirst'
theorem two (deletions produced front childRow row first second : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add (suc (suc z)) deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (suc deletions) produced)))
 (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second deletions produced)))
 : Supplier body Delta (suc (suc z)) deletions produced first second row := by
 apply fromData (suc (suc z)) deletions produced front childRow first second row hl hf hp hr
 intro beta j Theta old results hi ha
 have hl' := renameInto hl j Theta hi
 have hfirst' := renameInto hfirst j Theta hi
 have hsecond' := renameInto hsecond j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph2Rename,sucRelabel,zRelabel] at hl' hfirst' hsecond' ⊢
 have hlen := outputTransport OriginalContextInsertion.length
   (add (suc (suc z)) (deletions.relabel j)) (suc (suc (deletions.relabel j)))
   (Fin.cons (produced.relabel j) Fin.elim0) ⟨trans (leftSuccessor (suc z) (deletions.relabel j)) (congSuc (trans (leftSuccessor z (deletions.relabel j)) (congSuc (leftZero (deletions.relabel j)))))⟩ hl'
 exact UniformReturnSlotsProof.twoChildren
   (deletions.relabel j) (produced.relabel j) old results (first.relabel j) (second.relabel j) hlen ha hfirst' hsecond'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDataProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnDataProof
