module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchFrame
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261115 Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only actual parent observations and the discharged raw-induction hypothesis.
No child semantics, image membership, numerical bound or H calibration. -/
structure Frame (n : Nat) (H : Program 1) (arguments : Bool) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) where
  raw : OTerm alpha
  typ : OTerm alpha
  gamma : OTerm alpha
  pair : OTerm alpha
  size : OTerm alpha
  label : OTerm alpha
  depth : OTerm alpha
  guard : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))
  typed : Nonempty (Derivation body Delta (accepted H arguments typ raw gamma))
  bounds : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw))
  paired : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label))
  measured : Nonempty (Derivation body Delta (graph1 (OriginalEnumerationDepth.depth n) depth raw))
  ih : Nonempty (Derivation body Delta (BelowRaw n H raw))

variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

def Frame.conclusion (f : Frame n H arguments body alpha Delta) : Formula alpha := result arguments f.size f.depth

def Frame.rename (f : Frame n H arguments body alpha Delta) {beta : Type}
    (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Frame n H arguments body beta Theta where
  raw := f.raw.relabel j
  typ := f.typ.relabel j
  gamma := f.gamma.relabel j
  pair := f.pair.relabel j
  size := f.size.relabel j
  label := f.label.relabel j
  depth := f.depth.relabel j
  guard := by
    have h := renameInto f.guard j Theta hj
    simpa only [graph1Rename,sucRelabel,zRelabel] using h
  typed := by
    have h := renameInto f.typed j Theta hj
    rwa [SyntaxProof.acceptedRename] at h
  bounds := by
    have h := renameInto f.bounds j Theta hj
    rwa [graph1Rename] at h
  paired := by
    have h := renameInto f.paired j Theta hj
    rwa [graph2Rename] at h
  measured := by
    have h := renameInto f.measured j Theta hj
    rwa [graph1Rename] at h
  ih := by
    have h := renameInto f.ih j Theta hj
    rwa [InductionSyntaxProof.belowRawRename] at h

def Frame.addHyp (f : Frame n H arguments body alpha Delta) (A : Formula alpha) :
    Frame n H arguments body alpha (A :: Delta) where
  raw := f.raw
  typ := f.typ
  gamma := f.gamma
  pair := f.pair
  size := f.size
  label := f.label
  depth := f.depth
  guard := withHyp f.guard A
  typed := withHyp f.typed A
  bounds := withHyp f.bounds A
  paired := withHyp f.paired A
  measured := withHyp f.measured A
  ih := withHyp f.ih A

theorem conclusionRename (f : Frame n H arguments body alpha Delta) {beta : Type}
    (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    f.conclusion.relabel j = (f.rename j Theta hj).conclusion :=
  SyntaxProof.resultRename arguments f.size f.depth j

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchFrame
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchFrame
