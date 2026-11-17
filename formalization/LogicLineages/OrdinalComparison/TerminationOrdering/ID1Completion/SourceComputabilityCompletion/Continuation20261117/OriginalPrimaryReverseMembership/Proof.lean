module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.TargetQProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalPrimaryRerootInclusion (Request)
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem bound (n : Nat) (arity : Fin n → Nat)
    (seed parameter typ raw context gamma types out candidate targetOut : OTerm alpha)
    (q : Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut)
    : Nonempty (Derivation body Delta (graph2 contains (numeral 1) targetOut seed)) := by
  apply programCases (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta seedQ hj hseedQ
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hseedQ
  have q' := OriginalPrimaryRerootInclusion.RequestRenameProof.rename q j Theta hj
  exact TargetQProof.bound n arity (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (candidate.relabel j) (targetOut.relabel j) seedQ q'  hseedQ

theorem reverseMembership : Targets.InternalPrimaryReverseMembership := by
  intro n arity body alpha Delta seed parameter typ raw context gamma types out candidate targetOut hs hp hg ht hc ha hl hm htarget
  exact bound n arity seed parameter typ raw context gamma types out candidate targetOut ⟨hs,hp,hg,ht,hc,ha,hl,hm,htarget⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.Proof
