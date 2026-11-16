module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.ForwardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.BackwardProof
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

theorem atRetained (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate gamma value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (candidates n arity H) out seed param)))
    (hc : Nonempty (Derivation body Delta (OriginalClassCodes.Targets.meaning n arity H seed param candidate)))
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (hp : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value candidate gamma)))
    (hn : Nonempty (Derivation body Delta (eqn value (numeral 0)).not)) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalClassCodes.classCodes n arity H) ![seed,param] _
  intro beta j Theta cls hj hcls
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hx : (fun i => (![seed,param] i).relabel j) = (![seed.relabel j,param.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hcls
  have hh := renameInto h j Theta hj
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have hpj := renameInto hp j Theta hj
  have hnj := renameInto hn j Theta hj
  simp only [graph2Rename] at hh hgj hpj
  rw [OriginalClassCodes.MeaningRenameProof.meaningRename] at hcj
  simp only [Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof.notRename,eqnRelabel,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hf := InputProof.filterRecover n arity H (seed.relabel j) (param.relabel j) (out.relabel j) cls (gamma.relabel j) hh hcls hgj
  have hraw := (OriginalClassCodes.Proof.internalMembership n arity H body beta Theta (seed.relabel j) (param.relabel j) cls (candidate.relabel j) hcls).mpr hcj
  exact (Filter.FilterProof.internalFilter H body beta Theta cls (out.relabel j) (candidate.relabel j) (gamma.relabel j) z (value.relabel j) hf hpj).mpr (andIntro hraw hnj)

theorem backward (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 (candidates n arity H) out seed param)))
    (hm : Nonempty (Derivation body Delta
      (OriginalClassCodes.Targets.meaning n arity H seed param candidate ⊓ Targets.retained H seed param candidate))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) := by
  have hc := andLeft hm
  apply RetainedBindingProof.cases H seed param candidate _ (andRight hm)
  intro beta j Theta gamma value hj hg hp hn
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hh := renameInto h j Theta hj
  have hcj := renameInto hc j Theta hj
  rw [graph2Rename] at hh
  rw [OriginalClassCodes.MeaningRenameProof.meaningRename] at hcj
  exact atRetained n arity H (seed.relabel j) (param.relabel j) (out.relabel j) (candidate.relabel j) gamma value hh hcj hg hp hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.BackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.BackwardProof
