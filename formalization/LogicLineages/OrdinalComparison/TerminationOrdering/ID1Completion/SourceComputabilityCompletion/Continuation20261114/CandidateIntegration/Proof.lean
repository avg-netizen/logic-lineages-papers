module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipInstallationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipLeafSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary
attribute [local irreducible] programGraph

theorem retainedTuple : Targets.RetainedTuple := by
  intro n arity p H G W L hp hH hG hW hL
  have hd := TransparentCandidate.NativeProof.calibratedCandidate n arity H G hH hG
  obtain ⟨hprep,hretain⟩ := MembershipInstallationProof.actualRetainedInstallation
    n arity p H G W L (TransparentCandidate.candidate (OriginalTypedDecoder.target H G))
    hp hH hG hW hL hd
  exact ⟨hprep.1,hprep.2,hretain⟩

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨L,D,hL,_⟩ := MembershipLeafSelectionProof.actualLeafSelection n arity
  have hr := retainedTuple n arity p H G W L hp hH hG hW hL
  exact ⟨L,hL,hr.2.1,hr.2.2⟩

theorem classFactor : Targets.ClassFactor := by
  intro T L body alpha Delta seed input parameter list hL
  let D := TransparentCandidate.candidate T
  let xs : Fin 3 → OTerm alpha := ![seed,input,parameter]
  let target : Program 3 := .composition T ![.projection 1,.projection 2]
  let values : Program 3 := .composition L ![.projection 0,.projection 2]
  let decoded : Program 3 := .composition D ![.projection 1,.projection 2]
  constructor
  · intro h
    obtain ⟨hf⟩ := conjunctionRecover target (.composition Membership.contains ![values,decoded]) xs h
    have hT := binaryRecover T (.projection 1) (.projection 2) (suc z) input parameter xs
      ⟨Derivation.conjunctionLeft hf⟩ (projectionValue 1 xs) (projectionValue 2 xs)
    have hD := TransparentCandidate.InternalProof.acceptedValue T input parameter hT
    exact PrimaryMembership.Proof.classRecover T L D seed input parameter list input hL hD h
  · rintro ⟨h⟩
    have hT : Nonempty (Derivation body Delta (graph2 T (suc z) input parameter)) :=
      ⟨Derivation.conjunctionLeft h⟩
    have hD := TransparentCandidate.InternalProof.acceptedValue T input parameter hT
    exact MembershipInternalProof.actualInternalClassIntroduction T L D body alpha Delta
      seed input parameter list input hT hL hD ⟨Derivation.conjunctionRight h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
