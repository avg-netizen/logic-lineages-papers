module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem internalFactor : Targets.InternalFactor := by
  intro B body alpha Delta source target parameter a b ha hb
  let xs : Fin 3 → OTerm alpha := ![source,target,parameter]
  have ha' : Nonempty (Derivation body Delta (programGraph (typeField 0) a xs)) :=
    unaryValue InternalUnpair.left (.projection 0) a source xs ha (projectionValue 0 xs)
  have hb' : Nonempty (Derivation body Delta (programGraph (typeField 1) b xs)) :=
    unaryValue InternalUnpair.left (.projection 1) b target xs hb (projectionValue 1 xs)
  constructor
  · intro he
    obtain ⟨hc⟩ := conjunctionRecover typeGuard B xs he
    have hg := binaryRecover InternalEqualityTest.equalityTest (typeField 0) (typeField 1)
      (suc z) a b xs ⟨Derivation.conjunctionLeft hc⟩ ha' hb'
    obtain ⟨heq⟩ := InternalEqualityTestProof.equalityOfAcceptance a b hg
    exact ⟨Derivation.conjunctionIntroduction heq (Derivation.conjunctionRight hc)⟩
  · rintro ⟨h⟩
    have hg := InternalEqualityTestCompositionProof.equalityOfEqual a b ⟨Derivation.conjunctionLeft h⟩
    have ht := binaryValue InternalEqualityTest.equalityTest (typeField 0) (typeField 1)
      (suc z) a b xs hg ha' hb'
    exact conjunctionAccept typeGuard B xs ht ⟨Derivation.conjunctionRight h⟩

theorem internalMismatch : Targets.InternalMismatch := by
  intro B body alpha Delta source target parameter a b ha hb hn
  let A := graph3 (edge B) (suc z) source target parameter
  obtain ⟨hf⟩ := (internalFactor B body alpha (A :: Delta) source target parameter a b
    (withHyp ha A) (withHyp hb A)).mp ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := withHyp hn A
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination hn (Derivation.conjunctionLeft hf))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.InternalProof
