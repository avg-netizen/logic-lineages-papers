module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem memberTail (raw head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail needle))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle)) := by
  apply formulaCases (equal head needle)
  · exact containsHit raw head tail needle (withHyp hc _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact containsMiss raw head tail needle (numeral 1) (withHyp hc _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm _)

theorem pairCoordinates (entry node left right a b : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn entry node)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry left right)))
    (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node a b))) :
    Nonempty (Derivation body Delta (eqn a left ⊓ eqn b right)) := by
  have hp' := outputTransport InternalPairing.pairing entry node ![left,right] he hp
  have h1 := valueUnique InternalUnpair.left a left (Fin.cons node Fin.elim0)
    (pairLeft node a b hq) (pairLeft node left right hp')
  have h2 := valueUnique InternalUnpair.right b right (Fin.cons node Fin.elim0)
    (pairRight node a b hq) (pairRight node left right hp')
  exact andIntro h1 h2

theorem nilImpossible (step : Program 3) (raw param out node : OTerm alpha) (psi : Formula alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) step) out raw param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out node))) :
    Nonempty (Derivation body Delta psi) := by
  have hv0 := headTransport (InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) step)
    out raw z (Fin.cons param Fin.elim0) hz hv
  have h0 := InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) step z
    (Fin.cons param Fin.elim0) (InternalRawListRecursionSupportProof.constantZero (Fin.cons param Fin.elim0))
  have he := valueUnique (InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) step)
    out z ![z,param] hv0 h0
  have hm0 := headTransport contains (numeral 1) out z (Fin.cons node Fin.elim0) he hm
  obtain ⟨hn⟩ := valueUnique contains (numeral 1) z ![z,node] hm0 (containsNil node)
  exact ⟨Derivation.explosion (sucNeZeroApply hn)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.SupportProof
