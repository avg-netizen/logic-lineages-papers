module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.AdmissionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAcceptanceBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalAcceptanceSupportProof InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem memberNonzero (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (admitted n H) value seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  have he : Nonempty (Derivation body ((eqn value z) :: Delta) (eqn value z)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz := outputTransport (admitted n H) value z ![seed,param] he (withHyp ha _)
  have hzero := zeroBranchElim (admitted n H) (constant 2 0) (frontend n arity) out ![seed,param]
    hz (withHyp hc _)
  have ho := valueUnique (constant 2 0) out z ![seed,param] hzero (constantValue 0 ![seed,param])
  have hmz := headTransport contains (numeral 1) out z ![candidate] ho (withHyp hm _)
  obtain ⟨hf⟩ := valueUnique contains (numeral 1) z ![z,candidate] hmz (containsNil candidate)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hf)⟩

theorem forward (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (admitted n H) value seed param)))
    (hn : Nonempty (Derivation body Delta (eqn value z).not))
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param))) :
    Nonempty (Derivation body Delta (graph2 (frontend n arity) out seed param)) :=
  Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof.nonzeroBranch
    (admitted n H) (constant 2 0) (frontend n arity) out value ![seed,param] ha hn hc

theorem backward (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (admitted n H) value seed param)))
    (hn : Nonempty (Derivation body Delta (eqn value z).not))
    (hc : Nonempty (Derivation body Delta (graph2 (frontend n arity) out seed param))) :
    Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param)) := by
  apply zeroSuccessorCases Delta value _
  · obtain ⟨hn⟩ := withHyp hn (eqn value z)
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta k hj he
    rw [graph2Rename]
    have haj := renameInto ha j Theta hj
    have hcj := renameInto hc j Theta hj
    simp only [graph2Rename] at haj hcj
    exact successorBranchIntro (admitted n H) (constant 2 0) (frontend n arity) (out.relabel j) k
      ![seed.relabel j,param.relabel j]
      (outputTransport (admitted n H) (value.relabel j) (suc k) _ he haj) hcj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.AdmissionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.AdmissionProof
