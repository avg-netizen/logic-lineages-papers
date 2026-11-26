module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextWindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open OriginalInternalRawSameContextSupportProof
open OriginalContextInsertion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rawWindow (raw parameter window gamma jobs count index child : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs)))
 (hb : Nonempty (Derivation body Delta (Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index jobs))) :
 Nonempty (Derivation body Delta (graph1 windowSelector window child)) := by
 apply OriginalInternalRawExpansionLookupProof.actualCases body alpha Delta raw parameter jobs count index child _ he hl hb hv
 · intro beta rho Theta arity _ hrho _ _ hc
   simp only [graph1Rename]
   have hp' := renameInto hp rho Theta hrho
   rw [graph2Rename] at hp'
   exact firstWindow (raw.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (child.relabel rho) hp' hc
 · intro beta rho Theta hrho _ _ hc
   simp only [graph1Rename]
   have hp' := renameInto hp rho Theta hrho
   rw [graph2Rename] at hp'
   exact secondWindow (raw.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho) (child.relabel rho) hp' hc
 · intro beta rho Theta arity row cutoff size _ hrho _ _ hd hlen hbound hlookup
   simp only [graph1Rename]
   have hp' := renameInto hp rho Theta hrho
   rw [graph2Rename] at hp'
   apply OriginalHereditaryInternalDeletionLookupProof.actualLookup body beta Theta
     (raw.relabel rho) (parameter.relabel rho) row size cutoff (child.relabel rho) _ hd hlen hbound hlookup
   intro eta sigma Xi c context typ deleted erased childParameter hsigma hparam _ _ _ _ _ hcp hchild
   simp only [graph1Rename]
   have hp'' := renameInto hp' sigma Xi hsigma
   rw [graph2Rename] at hp''
   have heq := valueUnique InternalUnpair.left c ((window.relabel rho).relabel sigma)
     (Fin.cons ((parameter.relabel rho).relabel sigma) Fin.elim0)
     (pairLeft _ c context hparam) (pairLeft _ _ _ hp'')
   exact outputTransport windowSelector c ((window.relabel rho).relabel sigma)
     (Fin.cons ((child.relabel rho).relabel sigma) Fin.elim0) heq
     (fromPairs ((child.relabel rho).relabel sigma) erased childParameter c deleted hchild hcp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextWindowProof
