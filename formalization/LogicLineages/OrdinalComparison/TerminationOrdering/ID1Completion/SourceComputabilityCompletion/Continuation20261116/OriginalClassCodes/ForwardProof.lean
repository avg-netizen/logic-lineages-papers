module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairElimProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageEliminationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.ForwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn eqnRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type} {n : Nat} {arity : Fin n → Nat} {H : Program 1}
variable {body : Positive (Fin 1)} {Delta : List (Formula alpha)} {seed param : OTerm alpha}
attribute [local irreducible] programGraph

theorem atFrame (f : Frame n arity H body Delta seed param) (out candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta (Targets.meaning n arity H seed param candidate)) := by
  have hn := AdmissionProof.memberNonzero n arity H seed param out candidate (f.values 7) (f.graph 7) hc hm
  have hi := PairElimProof.recover (f.values 12) (f.values 0) out candidate (FrameProof.mapped f out hn hc) hm
  apply PairImageEliminationProof.cases (f.values 12) (f.values 0) candidate _ hi
  intro beta j Theta raw hj hmem hpair
  rw [MeaningRenameProof.meaningRename]
  have hnj := renameInto hn j Theta hj
  simp only [eqnRelabel,zRelabel,Continuation20261114.SourceHeadsFilterAdequacy.InductionSyntaxProof.notRename] at hnj
  exact FrameProof.meaning (FrameProof.rename f j Theta hj) (candidate.relabel j) raw hnj hpair hmem

theorem forward (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param out candidate : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate))) :
    Nonempty (Derivation body Delta (Targets.meaning n arity H seed param candidate)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n arity H) ![seed,param] _
  intro beta j ys Theta hj hv
  rw [MeaningRenameProof.meaningRename]
  have hx : (fun i => (![seed,param] i).relabel j) = (![seed.relabel j,param.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hv
  let f : Frame n arity H body Theta (seed.relabel j) (param.relabel j) := ⟨ys,hv⟩
  have hcj := renameInto hc j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj hmj
  exact atFrame f (out.relabel j) (candidate.relabel j) hcj hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.ForwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.ForwardProof
