module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ClauseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalCodeValidityGuard.FieldProof
open ClauseProof
variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}

theorem forward (f : Frame n body Delta raw) (table : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) table (suc raw) raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (Targets.allowed n f.tag f.payload f.first f.second f.head)) := by
  have hr := OriginalCodeValidityGuard.TableSupportProof.nextRowRecover n raw raw f.previous table f.prior ht
  have hl := SupportProof.checkRecover n raw table (suc z) ht ha
  have hs := OriginalCodeDecoderTable.Proof.internalRowLookup n body alpha Delta raw f.previous table raw (suc z)
    hr (ChildProof.selfBound raw) hl
  have hb := OriginalCodeDecoderStep.ForwardProof.forward n f.previous raw f.tag f.payload f.first f.second f.head
    f.pair (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph) hs
  exact ClauseProof.toOwn f hb

theorem backward (f : Frame n body Delta raw) (table : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) table (suc raw) raw)))
    (ha : Nonempty (Derivation body Delta (Targets.allowed n f.tag f.payload f.first f.second f.head))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)) := by
  have hr := OriginalCodeValidityGuard.TableSupportProof.nextRowRecover n raw raw f.previous table f.prior ht
  have hb := ClauseProof.fromOwn f ha
  have hs := OriginalCodeDecoderStep.BackwardProof.backward n f.previous raw f.tag f.payload f.first f.second f.head
    f.pair (firstAt _ _ _ f.firstGraph) (secondAt _ _ _ f.secondGraph) (headAt _ _ _ f.headGraph) hb
  have hl := OriginalCodeValidityGuard.TableSupportProof.rowLookupIntro n raw f.previous table raw (suc z)
    hr (ChildProof.selfBound raw) hs
  exact SupportProof.checkIntro n raw table (suc z) ht hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.CoreProof
