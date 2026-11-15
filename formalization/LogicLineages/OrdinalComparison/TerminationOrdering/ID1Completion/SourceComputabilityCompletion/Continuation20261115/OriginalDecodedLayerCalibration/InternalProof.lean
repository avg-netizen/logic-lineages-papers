module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nodeForward (n : Nat) (node answers param source target : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hv : Nonempty (Derivation body Delta (graph3 (nodeAccepted n) (numeral 1) node answers param))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source ⊓
       graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)) := by
  let xs : Fin 3 → OTerm alpha := ![node,answers,param]
  have h := binaryRecover (OriginalDecodedDependencies.accepted n) (.projection 0) (.projection 2)
    (numeral 1) node param xs hv (projectionValue 0 xs) (projectionValue 2 xs)
  have hc := conjunctionRecover (OriginalDecodedDependencies.sourceAccepted n) (OriginalDecodedDependencies.targetAccepted n) ![node,param] h
  have hs := unaryRecover (OriginalCodeValidityGuard.check n) OriginalDecodedDependencies.source
    (numeral 1) source ![node,param] (andLeft hc) (OriginalDecodedDependencies.SupportProof.sourceAt node param source target hp)
  have ht := unaryRecover (OriginalCodeValidityGuard.check n) OriginalDecodedDependencies.target
    (numeral 1) target ![node,param] (andRight hc) (OriginalDecodedDependencies.SupportProof.targetAt node param source target hp)
  exact andIntro hs ht

theorem nodeBackward (n : Nat) (node answers param source target : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target))) :
    Nonempty (Derivation body Delta (graph3 (nodeAccepted n) (numeral 1) node answers param)) := by
  have hc := conjunctionAccept (OriginalDecodedDependencies.sourceAccepted n) (OriginalDecodedDependencies.targetAccepted n) ![node,param]
    (OriginalDecodedDependencies.SupportProof.sourceAcceptedAt n node param source target (numeral 1) hp hs)
    (OriginalDecodedDependencies.SupportProof.targetAcceptedAt n node param source target (numeral 1) hp ht)
  exact binaryValue (OriginalDecodedDependencies.accepted n) (.projection 0) (.projection 2)
    (numeral 1) node param ![node,answers,param] hc (projectionValue 0 _) (projectionValue 2 _)

theorem windowForward (n : Nat) (node answers param symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hv : Nonempty (Derivation body Delta (graph3 (windowAccepted n) (numeral 1) node answers param))) :
    Nonempty (Derivation body Delta (OriginalDecodedWindowValidity.Targets.boundedMembers n symbols)) := by
  have hw := unaryRecover (OriginalDecodedWindowValidity.window n) (.projection 2)
    (numeral 1) param ![node,answers,param] hv (projectionValue 2 _)
  have hs := unaryRecover (OriginalDecodedWindowValidity.symbols n) InternalUnpair.left
    (numeral 1) symbols (Fin.cons param Fin.elim0) hw (pairLeft param symbols types hp)
  exact (OriginalDecodedWindowValidity.Proof.internalSymbols n body alpha Delta symbols).mp hs

theorem windowBackward (n : Nat) (node answers param symbols types : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hm : Nonempty (Derivation body Delta (OriginalDecodedWindowValidity.Targets.boundedMembers n symbols))) :
    Nonempty (Derivation body Delta (graph3 (windowAccepted n) (numeral 1) node answers param)) := by
  have hs := (OriginalDecodedWindowValidity.Proof.internalSymbols n body alpha Delta symbols).mpr hm
  have hw := unaryValue (OriginalDecodedWindowValidity.symbols n) InternalUnpair.left
    (numeral 1) symbols (Fin.cons param Fin.elim0) hs (pairLeft param symbols types hp)
  exact unaryValue (OriginalDecodedWindowValidity.window n) (.projection 2)
    (numeral 1) param ![node,answers,param] hw (projectionValue 2 _)

theorem internalGuard : Targets.InternalGuard := by
  intro n body alpha Delta node answers param source target symbols types hn hw
  constructor
  · intro hv
    have h := conjunctionRecover (nodeAccepted n) (windowAccepted n) ![node,answers,param] hv
    exact andIntro (nodeForward n node answers param source target hn (andLeft h))
      (windowForward n node answers param symbols types hw (andRight h))
  · intro h
    have hc := andLeft h
    exact conjunctionAccept (nodeAccepted n) (windowAccepted n) ![node,answers,param]
      (nodeBackward n node answers param source target hn (andLeft hc) (andRight hc))
      (windowBackward n node answers param symbols types hw (andRight h))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.InternalProof
