module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.InvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalTagArithmeticSupportProof (symm)
open InternalTagArithmeticSyntaxProof (z)

theorem accepted (n : Nat) (arity : Fin n → Nat)
    (singleton seed seedType seedRaw gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton seed z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)))
    (hu : Nonempty (Derivation body Delta (OriginalPrimaryUniverseClosure.accepted n arity seedType seedRaw gamma context))) :
    Nonempty (Derivation body Delta (allAccepted n arity singleton gamma context)) := by
  apply InvariantProof.introduce n arity singleton gamma context
  intro beta j Theta candidate typ raw hj hm hpair
  have hc' := renameInto hc j Theta hj
  simp only [graph2Rename,zRelabel] at hc'
  have hp' := renameInto hp j Theta hj
  rw [graph2Rename] at hp'
  have hu' := renameInto hu j Theta hj
  rw [acceptedRename] at hu'
  obtain ⟨he⟩ := PrimaryCarrierBound.RunProof.singletonMember
    (singleton.relabel j) (seed.relabel j) candidate hc' hm
  have heq := EqualityProof.pairFields (seed.relabel j) candidate
    (seedType.relabel j) (seedRaw.relabel j) typ raw hp' hpair ⟨symm he⟩
  exact EqualityProof.acceptedFields n arity (seedType.relabel j) typ (seedRaw.relabel j) raw
    (gamma.relabel j) (context.relabel j) (andLeft heq) (andRight heq) hu'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SingletonProof
