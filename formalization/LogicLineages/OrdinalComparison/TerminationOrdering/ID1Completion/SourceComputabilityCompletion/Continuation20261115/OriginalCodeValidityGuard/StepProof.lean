module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.FieldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SelectorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.AllowedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalOriginalOrderSyntaxProof InternalUnpairReverseBoundsArithmeticProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem monotone (n : Nat) (bound old next raw : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (RelationProof.relation bound old next)))
    (hb : Nonempty (Derivation body Delta (Below raw (suc bound))))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) (suc z) old raw))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) (suc z) next raw)) := by
  apply FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [RelationProof.relationRename] at hr'
  have hb' := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [Below,orderRename,sucRelabel] at hb'
  have ha' := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at ha'
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hfbound := SelectorBoundsProof.firstBounded (.projection 0) body beta Theta xs
    (raw.relabel j) first (projectionValue 0 xs) hf
  have hsbound := SelectorBoundsProof.secondBounded (.projection 0) body beta Theta xs
    (raw.relabel j) second (projectionValue 0 xs) hs
  have hfbelow := weakTrans first (raw.relabel j) (bound.relabel j) hfbound hb'
  have hsbelow := weakTrans second (raw.relabel j) (bound.relabel j) hsbound hb'
  have hold := OriginalCodeDecoderStep.ForwardProof.forward n (old.relabel j) (raw.relabel j)
    tag payload first second head hp (FieldProof.firstAt _ _ _ hf)
    (FieldProof.secondAt _ _ _ hs) (FieldProof.headAt _ _ _ hh) ha'
  have hnew := AllowedProof.transport n (bound.relabel j) (old.relabel j) (next.relabel j)
    tag payload first second head hr' hfbelow hsbelow hold
  exact OriginalCodeDecoderStep.BackwardProof.backward n (next.relabel j) (raw.relabel j)
    tag payload first second head hp (FieldProof.firstAt _ _ _ hf)
    (FieldProof.secondAt _ _ _ hs) (FieldProof.headAt _ _ _ hh) hnew
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.StepProof
