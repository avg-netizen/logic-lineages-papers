module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Types.AllowedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalEnumerationFields.Types.AllowedProof
open OriginalEnumerationFields.Types.AllowedSyntaxProof (allowedRename)
open OriginalTypeListsMembership.Targets (allMembers)
open OriginalTypeListsMembership.MemberProof (nilMembers consMembers)
open InternalAdditionLawsProof (add)
open InternalOriginalPairingOrderArithmeticProof (weakStrictTrans)
open InternalApplicationStepPeelSupportProof (andLeft)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open ArgumentEntriesDependencyDescent.SupportProof (strictRename)

theorem empty (raw allowed bound : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed raw allowed bound)) := by
  have hl := headTransport length z z raw Fin.elim0 ⟨symm (Classical.choice hz)⟩
    (lengthZero (body := body) (alpha := alpha) (Gamma := Delta))
  have hm := OriginalTypeListsMembership.ArithmeticProof.membersTransport z raw allowed
    ⟨symm (Classical.choice hz)⟩ (nilMembers allowed)
  exact introduce raw allowed bound z hl ⟨InternalQuotientComparisonProof.zeroLessSuccessor bound⟩ hm

theorem monotone (raw allowed small big : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed raw allowed small)))
    (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess small (suc big)))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed raw allowed big)) := by
  apply InternalAcceptanceSupportProof.programCases length (Fin.cons raw Fin.elim0) _
  intro beta j Theta len hj hl
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hl
  rw [allowedRename]
  have haj := renameInto ha j Theta hj
  have hbj := renameInto hb j Theta hj
  rw [allowedRename] at haj
  simp only [strictRename,sucRelabel] at hbj
  exact introduce (raw.relabel j) (allowed.relabel j) (big.relabel j) len hl
    (weakStrictTrans len (small.relabel j) (suc (big.relabel j)) (lengthBound _ _ _ len hl haj) hbj)
    (members _ _ _ haj)

theorem consAtLength (raw typ tail allowed headSize tailSize len : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw typ tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed typ)))
    (ha : Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed tail allowed tailSize)))
    (hp : Nonempty (Derivation body Delta (InternalLessThan.strictLess z headSize)))
    (hl : Nonempty (Derivation body Delta (lengthGraph len tail))) :
    Nonempty (Derivation body Delta
      (OriginalEnumerationFields.Targets.typesAllowed raw allowed (add headSize tailSize))) := by
  have htail := lengthBound tail allowed tailSize len hl ha
  have hsuc := OriginalEnumerationMembership.OrderProof.successorForward len (suc tailSize) htail
  have hroom := OriginalTypedEnumerationDepthBound.BinaryArithmeticProof.positiveTailRoom headSize tailSize hp
  have hbound := weakStrictTrans (suc len) (suc tailSize) (suc (add headSize tailSize)) hsuc hroom
  exact introduce raw allowed (add headSize tailSize) (suc len)
    (lengthCons raw typ tail len hc hl) hbound
    (consMembers raw typ tail allowed hc hm (members tail allowed tailSize ha))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypesProof
