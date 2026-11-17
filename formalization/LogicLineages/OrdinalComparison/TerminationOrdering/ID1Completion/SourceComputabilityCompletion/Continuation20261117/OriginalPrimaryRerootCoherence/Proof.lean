module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.ReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationStepPeelSupportProof (andIntro)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem primaryRerootCoherence : Targets.InternalPrimaryRerootCoherence := by
  intro n arity body alpha Delta seed parameter typ raw context gamma types out candidate targetOut hs hp hg ht hc ha hl hm htarget
  have hforward := OriginalPrimaryRerootInclusion.Proof.primaryRerootInclusion n arity body alpha Delta
    seed parameter typ raw context gamma types out candidate targetOut hs hp hg ht hc ha hl hm htarget
  have hreverse := ReverseProof.inclusion n arity seed parameter typ raw context gamma types out candidate targetOut ⟨hs,hp,hg,ht,hc,ha,hl,hm,htarget⟩
  exact andIntro hforward hreverse

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootCoherence.Proof
