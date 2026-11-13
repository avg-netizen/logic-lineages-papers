module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedIndexedLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildRawCellProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open OriginalContextInsertionSyntaxProof (lengthRename)
open InternalOriginalOrderSyntaxProof (orderRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual raw-cell extraction at the known parent coordinates. This is only
an elimination principle, with no source-validity or native-typing premise. -/
theorem rawCellCases (parent role typ typed rawJob raw parameter row count index child : OTerm alpha)
 (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (jobs cell : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 OriginalHereditaryExpansion.expansion jobs (raw.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph1 OriginalContextInsertion.length (count.relabel j) jobs)) →
   Nonempty (Derivation body Theta (OriginalContextInsertion.Below (index.relabel j) (count.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup cell (index.relabel j) jobs)) →
   Nonempty (Derivation body Theta (graph5 OriginalHereditaryAnnotatedExpansion.decorate (child.relabel j)
     (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) cell)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply programCases OriginalHereditaryExpansion.expansion xs psi
 intro beta j Theta jobs hj hraw
 have hx : (fun i => (xs i).relabel j) =
     Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hraw
 have hp' := renameInto hp j Theta hj
 have ht' := renameInto ht j Theta hj
 have hr' := renameInto hr j Theta hj
 have he' := renameInto he j Theta hj
 have hl' := renameInto hl j Theta hj
 have hb' := renameInto hb j Theta hj
 have hk' := renameInto hk j Theta hj
 simp only [graph1Rename,graph2Rename,OriginalContextInsertion.Below,orderRename] at hp' ht' hr' he' hl' hb' hk'
 have hd := SixSol20261113.Runtime.SourceFramedChildCoordinatesProof.decorateAllFromCoordinates
   (parent.relabel j) (role.relabel j) (typ.relabel j) (typed.relabel j) (rawJob.relabel j)
   (raw.relabel j) (parameter.relabel j) jobs (row.relabel j) hp' ht' hr' hraw he'
 apply SixSol20261113.Runtime.SourceFramedIndexedLookupProof.actualLookup body beta Theta
   (role.relabel j) (typ.relabel j) (raw.relabel j) jobs (row.relabel j)
   (count.relabel j) (index.relabel j) (child.relabel j) _ hd hl' hb' hk'
 intro gamma k Xi cell hkinc hlen hlook hdecor
 have hraw' := renameInto hraw k Xi hkinc
 have hb'' := renameInto hb' k Xi hkinc
 simp only [graph2Rename,OriginalContextInsertion.Below,orderRename] at hraw' hb''
 have hn := next gamma (k ∘ j) Xi (jobs.relabel k) cell
   (fun f hf => by simpa only [← formulaRelabelComposition] using hkinc (f.relabel j) (hj f hf))
 have hv := hn (by simpa only [Term.relabel_relabel] using hraw')
   (by simpa only [Term.relabel_relabel,OriginalContextInsertion.lengthGraph,graph1] using hlen)
   (by simpa only [Term.relabel_relabel,OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.ltF] using hb'')
   (by simpa only [Term.relabel_relabel] using hlook)
   (by simpa only [Term.relabel_relabel] using hdecor)
 simpa only [formulaRelabelComposition] using hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildRawCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildRawCellProof
