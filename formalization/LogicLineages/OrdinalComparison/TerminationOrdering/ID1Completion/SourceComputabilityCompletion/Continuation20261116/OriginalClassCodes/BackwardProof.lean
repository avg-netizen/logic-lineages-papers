module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameBackwardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningRenameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.BackwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type} {n : Nat} {arity : Fin n → Nat} {H : Program 1}
variable {body : Positive (Fin 1)} {Delta : List (Formula alpha)} {seed param : OTerm alpha}
attribute [local irreducible] programGraph

theorem atObservations (out candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (Meaning.observations n arity H seed param candidate xs)))
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (FrameBackwardProof.tailQueries n arity) ![seed,param] _
  intro beta j ys Theta hj hv
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hx : (fun i => (![seed,param] i).relabel j) = (![seed.relabel j,param.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hv
  have hh := renameInto h j Theta hj
  rw [MeaningRenameProof.observationsRename] at hh
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  exact FrameBackwardProof.atValues (fun i => (xs i).relabel j) ys (out.relabel j) hh hv hcj

theorem backward (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param)))
    (h : Nonempty (Derivation body Delta (Targets.meaning n arity H seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) := by
  apply MeaningBindingProof.cases n arity H seed param candidate _ h
  intro beta j Theta xs hj hh
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  exact atObservations (out.relabel j) (candidate.relabel j) xs hh hcj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.BackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.BackwardProof
