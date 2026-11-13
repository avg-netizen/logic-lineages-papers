module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedDeletionLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (pairRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem deletionLength (raw parameter window gamma count row : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
 (hr : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter))) :
 Nonempty (Derivation body Delta (lengthGraph count row)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons z (Fin.cons raw Fin.elim0)
 apply programCases InternalPairing.pairing xs _
 intro beta rho Theta fake hrho hf
 simp only [lengthRename]
 let xx : Fin 2 → OTerm beta := Fin.cons z (Fin.cons (raw.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
   · simp only [xs, xx, Fin.cons_zero, zRelabel]
   · rfl
 rw [hx] at hf
 have hp' := renameInto hp rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 simp only [graph2Rename,lengthRename] at hp' hl' hr'
 have hrows := OriginalHereditaryInternalDeletionLookupSupportProof.rowsAtFake
   (raw.relabel rho) (parameter.relabel rho) (row.relabel rho) fake hf hr'
 have hscan := OriginalHereditaryDeletionRowsBoundProof.scanFromRows OriginalHereditaryExpansion.unpackJob
   fake (parameter.relabel rho) (gamma.relabel rho) (count.relabel rho) (row.relabel rho)
   (pairRight (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) hp') hl' hrows
 exact OriginalHereditaryDeletionRowsScanLengthProof.scanLength OriginalHereditaryExpansion.unpackJob
   (count.relabel rho) fake (parameter.relabel rho) (row.relabel rho) hscan

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedDeletionLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedDeletionLengthProof
