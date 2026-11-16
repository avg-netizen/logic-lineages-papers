module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ChildInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115 Induction InductionBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem childResult (n : Nat) (H : Program 1) (arguments : Bool)
    (raw child typ gamma pair size label depth : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw)))
    (hsmall : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) child)))
    (ht : Nonempty (Derivation body Delta (accepted H arguments typ child gamma)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label)))
    (hd : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth child))) :
    Nonempty (Derivation body Delta (result arguments size depth)) := by
  have hf : Nonempty (Derivation body Delta
      (observations n H arguments child ![typ,gamma,pair,size,label,depth])) :=
    andIntro (andIntro (andIntro (andIntro hg ht) hb) hp) hd
  exact atRawApply n H arguments child ![typ,gamma,pair,size,label,depth]
    (belowRawAt n H raw child ih hsmall) hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ChildInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ChildInductionProof
