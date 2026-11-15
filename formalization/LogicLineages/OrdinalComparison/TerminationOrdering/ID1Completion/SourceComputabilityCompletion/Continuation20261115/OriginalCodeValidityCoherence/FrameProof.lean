module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.SideProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.FieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.FrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalRawSyntaxTransport
open SideProof InductionDefinitions InductionSyntaxProof

structure Frame (n : Nat) (body : Positive (Fin 1)) {alpha : Type}
    (Delta : List (Formula alpha)) (raw : OTerm alpha) where
  s1 : Side n body Delta raw
  s2 : Side n body Delta raw
  ih : Nonempty (Derivation body Delta (BelowRaw n raw))
  tag : OTerm alpha
  payload : OTerm alpha
  first : OTerm alpha
  second : OTerm alpha
  head : OTerm alpha
  pair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))
  firstGraph : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw))
  secondGraph : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))
  headGraph : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) head raw))
variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}

def Frame.withHyp (f : Frame n body Delta raw) (A : Formula alpha) : Frame n body (A :: Delta) raw where
  s1 := f.s1.withHyp A
  s2 := f.s2.withHyp A
  ih := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.ih A
  tag := f.tag
  payload := f.payload
  first := f.first
  second := f.second
  head := f.head
  pair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.pair A
  firstGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.firstGraph A
  secondGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.secondGraph A
  headGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.headGraph A

def Frame.rename {beta : Type} (f : Frame n body Delta raw) (j : alpha → beta)
    (Theta : List (Formula beta)) (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) : Frame n body Theta (raw.relabel j) where
  s1 := f.s1.rename j Theta hj
  s2 := f.s2.rename j Theta hj
  ih := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.ih j Theta hj
    simpa only [belowRawRename] using h
  tag := f.tag.relabel j
  payload := f.payload.relabel j
  first := f.first.relabel j
  second := f.second.relabel j
  head := f.head.relabel j
  pair := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.pair j Theta hj
    simpa only [graph2Rename] using h
  firstGraph := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.firstGraph j Theta hj
    simpa only [graph1Rename] using h
  secondGraph := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.secondGraph j Theta hj
    simpa only [graph1Rename] using h
  headGraph := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto f.headGraph j Theta hj
    simpa only [graph1Rename] using h

theorem transferFirst (f : Frame n body Delta raw)
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess f.first raw)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) f.first f.s1.previous))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) f.first f.s2.previous)) :=
  SideProof.transferChild f.s1 f.s2 f.first f.ih hc hl

theorem transferSecond (f : Frame n body Delta raw)
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess f.second raw)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) f.second f.s1.previous))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) f.second f.s2.previous)) :=
  SideProof.transferChild f.s1 f.s2 f.second f.ih hc hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.FrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.FrameProof
