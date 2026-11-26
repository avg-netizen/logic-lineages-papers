module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InternalRecursionGraphStepSyntaxProof (consTermRename)

def control (n : Nat) : Program 2 := .composition
  (Continuation20261115.OriginalDecodedContextValidity.contextGuard n) (fun _ : Fin 1 => .projection 1)
def selected : Program 2 := .composition contains
  ![.composition contextTypes (fun _ : Fin 1 => .projection 1),.projection 0]

theorem atControl (n : Nat) (typ context types value : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (control n) value typ context)))
    (hm : Nonempty (Derivation body Delta (graph2 (member n) (suc z) typ context)))
    (ht : Nonempty (Derivation body Delta (graph1 contextTypes types context))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) types typ)) := by
  let xs : Fin 2 → OTerm alpha := ![typ,context]
  have hn : Nonempty (Derivation body Delta (eqn value z).not) := by
    have he : Nonempty (Derivation body (eqn value z :: Delta) (eqn value z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := outputTransport (control n) value z xs he (withHyp hv _)
    have hzero := zeroBranchElim (control n) (constant 2 0) selected (suc z) xs hz (withHyp hm _)
    obtain ⟨heq⟩ := valueUnique (constant 2 0) (suc z) z xs hzero (constantValue 0 xs)
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply heq)⟩
  have hs := Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof.nonzeroBranch
    (control n) (constant 2 0) selected (suc z) value xs hv hn hm
  have htypes := unaryValue contextTypes (.projection 1) types context xs ht (projectionValue 1 xs)
  exact binaryRecover contains (.composition contextTypes (fun _ : Fin 1 => .projection 1))
    (.projection 0) (suc z) types typ xs hs htypes (projectionValue 0 xs)

theorem membership (n : Nat) (typ context types : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 (member n) (suc z) typ context)))
    (ht : Nonempty (Derivation body Delta (graph1 contextTypes types context))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) types typ)) := by
  apply programCases (control n) ![typ,context] _
  intro beta j Theta value hj hv
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hmj := renameInto hm j Theta hj
  have htj := renameInto ht j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at hmj htj
  have hvec : (fun i => (![typ,context] i).relabel j) = ![typ.relabel j,context.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hvec] at hv
  exact atControl n (typ.relabel j) (context.relabel j) (types.relabel j) value hv hmj htj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.MemberProof
