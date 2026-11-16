module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.MeaningPartsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.AdmissionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type} {n : Nat} {arity : Fin n → Nat} {H : Program 1}
variable {body : Positive (Fin 1)} {Delta : List (Formula alpha)} {seed param : OTerm alpha}
attribute [local irreducible] programGraph

def rename (f : Frame n arity H body Delta seed param) {beta : Type} (j : alpha → beta)
    (Theta : List (Formula beta)) (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Frame n arity H body Theta (seed.relabel j) (param.relabel j) where
  values := fun i => (f.values i).relabel j
  graph := by
    intro i
    have h := renameInto (f.graph i) j Theta hj
    rw [graph2Rename] at h
    exact h

theorem characterize (f : Frame n arity H body Delta seed param) (raw : OTerm alpha) :
    (Nonempty (Derivation body Delta (graph2 contains (numeral 1) (f.values 12) raw)) ↔
     Nonempty (Derivation body Delta
      (OriginalEnumerationFields.Targets.accepted n raw (f.values 5) (f.values 1) (f.values 2) (f.values 4) (f.values 3) ⊓
       OriginalEnumerationMembership.Targets.depthBound n raw (f.values 6)))) :=
  OriginalEnumerationMembership.Proof.internalMembership n body alpha Delta
    (f.values 8) (f.values 9) (f.values 10) (f.values 11) (f.values 12) raw
    (f.values 5) (f.values 6) (f.values 1) (f.values 2) (f.values 4) (f.values 3)
    (InputProof.nodeRecover n seed param _ _ _ (f.graph 8) (f.graph 5) (f.graph 6))
    (InputProof.parameterRecover n arity seed param _ _ _ (f.graph 9) (f.graph 1) (f.graph 10))
    (InputProof.middleRecover n arity seed param _ _ _ (f.graph 10) (f.graph 2) (f.graph 11))
    (InputProof.tailRecover n seed param _ _ _ (f.graph 11) (f.graph 4) (f.graph 3))
    (InputProof.enumerationRecover n arity seed param _ _ _ (f.graph 12) (f.graph 8) (f.graph 9))

theorem mapped (f : Frame n arity H body Delta seed param) (out : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn (f.values 7) z).not))
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param))) :
    Nonempty (Derivation body Delta (graph2 pairRoots out (f.values 12) (f.values 0))) :=
  InputProof.frontendRecover n arity seed param out _ _
    (AdmissionProof.forward n arity H seed param out (f.values 7) (f.graph 7) hn hc)
    (f.graph 12) (f.graph 0)

theorem meaning (f : Frame n arity H body Delta seed param) (candidate raw : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn (f.values 7) z).not))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (f.values 0) raw)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (f.values 12) raw))) :
    Nonempty (Derivation body Delta (Targets.meaning n arity H seed param candidate)) := by
  have hf := (characterize f raw).mp hm
  apply MeaningBindingProof.introduce n arity H seed param candidate
    ![raw,f.values 0,f.values 1,f.values 2,f.values 3,f.values 4,f.values 5,f.values 6,f.values 7]
  exact MeaningPartsProof.assemble n arity H seed param candidate _
    (f.graph 0) (f.graph 1) (f.graph 2) (f.graph 3) (f.graph 4) (f.graph 5) (f.graph 6)
    (f.graph 7) hn hp (andLeft hf) (andRight hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameProof
