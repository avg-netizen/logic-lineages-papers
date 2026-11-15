module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.SeedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.TableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open PersistenceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (n : Nat) (bound previous next index : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n z bound previous next index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index next)) := by
  have hs := TableSupportProof.zeroSeed n bound previous (andLeft (andLeft hf))
  have hl := SeedProof.seedLookup bound previous index (andLeft (andRight hf)) hs
  obtain ⟨he⟩ := valueUnique InternalRawListRecursion.lookup (suc z) z
    (Fin.cons index (Fin.cons previous Fin.elim0)) (andRight (andRight hf)) hl
  exact ⟨Derivation.explosion (Derivation.implicationElimination (sucNeZero z) he)⟩

theorem succCore (n : Nat) (fuel bound previous next index : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row n fuel)))
    (hf : Nonempty (Derivation body Delta (fields n (suc fuel) bound previous next index))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index next)) := by
  apply InternalAcceptanceSupportProof.programCases (OriginalCodeDecoderTable.tableProgram n)
    (Fin.cons fuel (Fin.cons bound Fin.elim0)) _
  intro beta j Theta earlier hj he
  simp only [graph2Rename,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at he
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  have hold := andLeft (andLeft hf')
  have hnext := andRight (andLeft hf')
  have hb := andLeft (andRight hf')
  have hlook := andRight (andRight hf')
  have hrel := RelationProof.fromRow n (fuel.relabel j) (bound.relabel j)
    earlier (previous.relabel j) hr' he hold
  have hrowOld := TableSupportProof.nextRowRecover n (fuel.relabel j) (bound.relabel j)
    earlier (previous.relabel j) he hold
  have hstepOld := OriginalCodeDecoderTable.Proof.internalRowLookup n body beta Theta
    (bound.relabel j) earlier (previous.relabel j) (index.relabel j) (suc z) hrowOld hb hlook
  have hstepNew := StepProof.monotone n (bound.relabel j) earlier (previous.relabel j)
    (index.relabel j) hrel hb hstepOld
  have hrowNew := TableSupportProof.nextRowRecover n (suc (fuel.relabel j)) (bound.relabel j)
    (previous.relabel j) (next.relabel j) hold hnext
  exact TableSupportProof.rowLookupIntro n (bound.relabel j) (previous.relabel j) (next.relabel j)
    (index.relabel j) (suc z) hrowNew hb hstepNew
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.CoreProof
