module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)

@[simp] theorem predecessorRename {beta : Type} (D : Program 2) (raw child param : OTerm alpha) (j : alpha → beta) :
    (predecessor D raw child param).relabel j = predecessor D (raw.relabel j) (child.relabel j) (param.relabel j) :=
  PrimaryExpansionSoundness.WitnessProof.witnessRename (dependencyEdge D) raw child param j

theorem observe (D : Program 2) (node param deps child : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child))) :
    Nonempty (Derivation body Delta (graph3 (dependencyEdge D) (numeral 1) node child param)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons node (Fin.cons child (Fin.cons param Fin.elim0))
  have hg := binaryValue D (.projection 0) (.projection 2) deps node param xs hd
    (projectionValue 0 xs) (projectionValue 2 xs)
  exact binaryValue contains (.composition D ![.projection 0,.projection 2]) (.projection 1)
    (numeral 1) deps child xs hm hg (projectionValue 1 xs)

theorem atDeps (D : Program 2) (raw head tail param out child rest deps : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)))
    (hr : Nonempty (Derivation body Delta (graph2 (ExchangeFrontier.flatten D) rest tail param)))
    (hs : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.flattenStep D) out head rest param)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps head param))) :
    Nonempty (Derivation body Delta (predecessor D raw child param)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons head (Fin.cons rest (Fin.cons param Fin.elim0))
  have hp := binaryValue D (.projection 0) (.projection 2) deps head param xs hd
    (projectionValue 0 xs) (projectionValue 2 xs)
  have ha := binaryRecover InternalApplicationValidityStackAppend.append
    (.composition D ![.projection 0,.projection 2]) (.projection 1) out deps rest xs hs hp (projectionValue 1 xs)
  have hsplit := PrimaryExpansionSoundness.AppendProof.appendPreservation deps rest out child ha hm
  apply orCases hsplit
  · intro Theta inc hleft
    have he : Nonempty (Derivation body Theta (equal head head)) := by
      rw [equalEqn]
      exact ⟨InternalTagArithmeticSupportProof.refl head⟩
    exact PrimaryExpansionSoundness.WitnessProof.introduction (dependencyEdge D) raw child param head
      (containsHit raw head tail head (weakenProof hc inc) he)
      (observe D head param deps child (weakenProof hd inc) hleft)
  · intro Theta inc hright
    have hw := belowRawApply D raw tail param rest child (weakenProof hb inc)
      (consTailDescent raw head tail (weakenProof hc inc)) (andIntro (weakenProof hr inc) hright)
    exact PrimaryExpansionSoundness.WitnessProof.prepend (dependencyEdge D) raw head tail child param (weakenProof hc inc) hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.SupportProof
