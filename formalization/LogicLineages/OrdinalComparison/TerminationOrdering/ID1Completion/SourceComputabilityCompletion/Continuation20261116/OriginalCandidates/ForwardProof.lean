module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.InputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.FilterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.ForwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn eqnRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type} {body : Positive (Fin 1)} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValues (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate cls gamma value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (candidates n arity H) out seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.classCodes n arity H) cls seed param)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (hp : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value candidate gamma)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta
      (OriginalClassCodes.Targets.meaning n arity H seed param candidate ⊓ Targets.retained H seed param candidate)) := by
  have hf := InputProof.filterRecover n arity H seed param out cls gamma h hc hg
  have hq := (Filter.FilterProof.internalFilter H body alpha Delta cls out candidate gamma z value hf hp).mp hm
  have hclass := (OriginalClassCodes.Proof.internalMembership n arity H body alpha Delta seed param cls candidate hc).mp (andLeft hq)
  exact andIntro hclass (RetainedBindingProof.introduce H seed param candidate gamma value hg hp (andRight hq))

theorem forward (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (candidates n arity H) out seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta
      (OriginalClassCodes.Targets.meaning n arity H seed param candidate ⊓ Targets.retained H seed param candidate)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (InputProof.queries n arity H) ![seed,param,candidate] _
  intro beta j ys Theta hj hv
  simp only [conjunctionRename,OriginalClassCodes.MeaningRenameProof.meaningRename,RetainedSyntaxProof.retainedRename]
  have hx : (fun i => (![seed,param,candidate] i).relabel j) =
      (![seed.relabel j,param.relabel j,candidate.relabel j] : Fin 3 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hv
  have hc := InputProof.classRecover n arity H (seed.relabel j) (param.relabel j) (candidate.relabel j) (ys 0) (hv 0)
  have hg := InputProof.gammaRecover (seed.relabel j) (param.relabel j) (candidate.relabel j) (ys 1) (hv 1)
  have hp := InputProof.checkRecover H (seed.relabel j) (param.relabel j) (candidate.relabel j) (ys 1) (ys 2) (hv 2) (hv 1)
  have hh := renameInto h j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hh hmj
  exact atValues n arity H (seed.relabel j) (param.relabel j) (out.relabel j) (candidate.relabel j) (ys 0) (ys 1) (ys 2) hh hc hg hp hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.ForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.ForwardProof
