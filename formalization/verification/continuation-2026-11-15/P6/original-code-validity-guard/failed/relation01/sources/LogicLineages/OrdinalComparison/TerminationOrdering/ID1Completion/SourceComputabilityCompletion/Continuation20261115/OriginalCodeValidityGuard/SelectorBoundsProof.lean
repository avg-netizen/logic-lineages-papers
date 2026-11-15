module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SelectorBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphProof InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalSquareRootArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalPairingSumBounds
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorPairBoundsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Private graph property over every original context, not a public supplier assumption. -/
def Bounded {k : Nat} (raw selector : Program k) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (xs : Fin k → OTerm alpha) (input output : OTerm alpha),
    Nonempty (Derivation body Delta (programGraph raw input xs)) →
    Nonempty (Derivation body Delta (programGraph selector output xs)) →
    Nonempty (Derivation body Delta (weakBound output input))

theorem boundedPath {k : Nat} (raw : Program k) (path : List Bool) : Bounded raw (pathQuery path raw) := by
  intro body alpha Delta xs input output hr hs
  exact pathBound path raw input output xs hr hs

theorem boundedBranch {k : Nat} (raw control left right : Program k)
    (hl : Bounded raw left) (hr : Bounded raw right) :
    Bounded raw (InternalAcceptance.branch control left right) := by
  intro body alpha Delta xs input output hraw hsel
  apply programCompositionCases GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons left (Fin.cons right Fin.elim0))) output xs _ hsel
  intro beta j ys Theta hj ht hg
  rw [weakRename]
  have hraw' := InternalGraphCompositionFunctionalityProof.renameInto hraw j Theta hj
  rw [InternalControlGraphSupportProof.programRename] at hraw'
  have ha := hl body beta Theta (fun i => (xs i).relabel j) (input.relabel j) (ys 1) hraw' (hg 1)
  have hb := hr body beta Theta (fun i => (xs i).relabel j) (input.relabel j) (ys 2) hraw' (hg 2)
  apply formulaCases (eqn (ys 0) z)
  · let A := eqn (ys 0) z
    have hv := conditionalAtZero (body := body) (Gamma := A :: Theta) (ys 0) (ys 1) (ys 2)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [threeTuple] at hv
    obtain ⟨he⟩ := valueUnique GorbowPRInternalControl.conditional (output.relabel j) (ys 1) ys (withHyp ht A) hv
    obtain ⟨ha⟩ := withHyp ha A
    exact ⟨orderLeft (suc (input.relabel j)) (symm he) ha⟩
  · let A := (eqn (ys 0) z).not
    have hv := conditionalAtNonzero (body := body) (Gamma := A :: Theta) (ys 0) (ys 1) (ys 2)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    rw [threeTuple] at hv
    obtain ⟨he⟩ := valueUnique GorbowPRInternalControl.conditional (output.relabel j) (ys 2) ys (withHyp ht A) hv
    obtain ⟨hb⟩ := withHyp hb A
    exact ⟨orderLeft (suc (input.relabel j)) (symm he) hb⟩

theorem firstBounded {k : Nat} (raw : Program k) : Bounded raw (firstOf raw) := by
  unfold firstOf
  apply boundedBranch
  · apply boundedBranch
    · apply boundedBranch
      · exact boundedPath raw [true,true,false]
      · exact boundedPath raw [true,true,true,true,false]
    · exact boundedPath raw [true,true]
  · exact boundedPath raw [true,true]

theorem secondBounded {k : Nat} (raw : Program k) : Bounded raw (secondOf raw) := by
  unfold secondOf
  apply boundedBranch
  · exact boundedPath raw [true,true,true]
  · exact boundedPath raw [true,true,true,true,true,true]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SelectorBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SelectorBoundsProof
