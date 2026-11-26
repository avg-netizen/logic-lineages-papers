module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberProof
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
open Continuation20261114
variable {n : Nat}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open MemberSupportProof

theorem unary1 (raw deps child first : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 1) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)))
    : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons first (Fin.cons z (Fin.elim0))) _
  intro beta j Theta listCode hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  exact MemberSupportProof.unaryAt (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) listCode haj hdj hmj hfirstj hx hvj

theorem binary3 (raw deps child first second rest : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hsecond : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second raw)))
    (hrest : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest second z)))
    (hv1 : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)))
    (hv2 : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)))
    : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons first (Fin.cons rest (Fin.elim0))) _
  intro beta j Theta listCode hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  have hsecondj := renameInto hsecond j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsecondj
  have hrestj := renameInto hrest j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hrestj
  have hv1j := renameInto hv1 j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := renameInto hv2 j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hv2j
  exact MemberSupportProof.binaryAt (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) (second.relabel j) (rest.relabel j) listCode haj hdj hmj hfirstj hsecondj hrestj hx hv1j hv2j

theorem binary2 (raw deps child first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral 2) raw)))
    (hd : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hfirst : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first raw)))
    (hsecond : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second raw)))
    (hv1 : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)))
    (hv2 : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)))
    : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)) := by
  apply programCases (InternalListCodec.consCode) (Fin.cons second (Fin.cons z (Fin.elim0))) _
  intro beta j Theta rest hj hx
  simp only [consTermRename,emptyRename,zRelabel] at hx
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have haj := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at haj
  have hdj := renameInto hd j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hdj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hfirstj := renameInto hfirst j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hfirstj
  have hsecondj := renameInto hsecond j Theta hj
  simp only [graph1Rename,graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hsecondj
  have hv1j := renameInto hv1 j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hv1j
  have hv2j := renameInto hv2 j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hv2j
  exact binary3 (raw.relabel j) (deps.relabel j) (child.relabel j) (first.relabel j) (second.relabel j) rest haj hdj hmj hfirstj hsecondj hx hv1j hv2j

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberProof
