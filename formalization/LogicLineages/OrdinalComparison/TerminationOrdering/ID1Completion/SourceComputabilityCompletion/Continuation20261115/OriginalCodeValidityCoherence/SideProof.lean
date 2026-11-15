module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.StageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.SideProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalOriginalOrderSyntaxProof
open OriginalContextInsertionSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InductionDefinitions

structure Side (n : Nat) (body : Positive (Fin 1)) {alpha : Type}
    (Delta : List (Formula alpha)) (raw : OTerm alpha) where
  bound : OTerm alpha
  predecessor : OTerm alpha
  previous : OTerm alpha
  table : OTerm alpha
  bounded : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc bound)))
  enough : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc predecessor)))
  prior : Nonempty (Derivation body Delta
    (graph2 (OriginalCodeDecoderTable.tableProgram n) previous predecessor bound))
  row : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.nextRow n) table bound previous))

variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}

def Side.rename {beta : Type} (s : Side n body Delta raw) (j : alpha → beta)
    (Theta : List (Formula beta)) (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) : Side n body Theta (raw.relabel j) where
  bound := s.bound.relabel j
  predecessor := s.predecessor.relabel j
  previous := s.previous.relabel j
  table := s.table.relabel j
  bounded := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.bounded j Theta hj
    simpa only [InternalLessThan.strictLess,orderRename,sucRelabel] using h
  enough := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.enough j Theta hj
    simpa only [InternalLessThan.strictLess,orderRename,sucRelabel] using h
  prior := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.prior j Theta hj
    simpa only [graph2Rename] using h
  row := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto s.row j Theta hj
    simpa only [graph2Rename] using h

def Side.withHyp (s : Side n body Delta raw) (A : Formula alpha) : Side n body (A :: Delta) raw where
  bound := s.bound
  predecessor := s.predecessor
  previous := s.previous
  table := s.table
  bounded := InternalApplicationValidityStackAppendInductionCoreProof.withHyp s.bounded A
  enough := InternalApplicationValidityStackAppendInductionCoreProof.withHyp s.enough A
  prior := InternalApplicationValidityStackAppendInductionCoreProof.withHyp s.prior A
  row := InternalApplicationValidityStackAppendInductionCoreProof.withHyp s.row A

theorem transferChild (s1 s2 : Side n body Delta raw) (child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw n raw)))
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) child s1.previous))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) child s2.previous)) := by
  have hb1 := StageProof.childBound child raw s1.bound hc s1.bounded
  have hb2 := StageProof.childBound child raw s2.bound hc s2.bounded
  have hf1 := StageProof.childFuel child raw s1.predecessor hc s1.enough
  have hf2 := StageProof.childFuel child raw s2.predecessor hc s2.enough
  exact BindingProof.belowRawApply n raw child s1.predecessor s1.bound s1.previous
    s2.predecessor s2.bound s2.previous hi hc
    (andIntro (andIntro (andIntro hb1 hb2) (andIntro hf1 hf2)) (andIntro (andIntro s1.prior s2.prior) hl))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.SideProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.SideProof
