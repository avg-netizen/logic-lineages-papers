module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalTypedDecoderTransport
open InternalTagArithmeticSyntaxProof (suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both transformations retain the lambda's literal domain and recurse only
into its body at successor cutoff. -/
theorem lambdaShape (erasing : Bool) (raw out d k domain child childOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hchild : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) childOut d (suc k) child)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta (graph2 lambdaConstructor out domain childOut)) := by
  have h := OriginalRawSyntaxTransportInternalFoldLambdaProof.lambdaForward
    (selectedMode erasing) raw out d k domain child childOut hc hchild ho
  cases erasing <;> exact h

theorem applicationShape (erasing : Bool) (raw out d k domain fn arg fnOut argOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
    (hf : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) fnOut d k fn)))
    (ha : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) argOut d k arg)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta (graph3 applicationConstructor out domain fnOut argOut)) := by
  have h := OriginalRawSyntaxTransportInternalFoldApplicationProof.applicationForward
    (selectedMode erasing) raw out d k domain fn arg fnOut argOut hc hf ha ho
  cases erasing <;> exact h

theorem ordinaryShape (erasing : Bool) (raw out d k head base baseOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hb : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) baseOut d k base)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta (graph2 ordinaryConstructor out head baseOut)) := by
  have h := OriginalRawSyntaxTransportInternalFoldOrdinaryProof.ordinaryForward
    (selectedMode erasing) raw out d k head base baseOut hc hb ho
  cases erasing <;> exact h

/-- Label, head, recorded result and extra type-list are ALL retained. The
head's result type is not substituted for the recorded result. -/
theorem numberedShape (erasing : Bool)
    (raw out d k label head recorded base types extras baseOut extrasOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor raw ![label,head,recorded,base,types,extras])))
    (hb : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) baseOut d k base)))
    (he : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) extrasOut d k extras)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta
      (programGraph numberedConstructor out ![label,head,recorded,baseOut,types,extrasOut])) := by
  have h := OriginalRawSyntaxTransportInternalFoldNumberedProof.numberedForward
    (selectedMode erasing) raw out d k label head recorded base types extras baseOut extrasOut hc hb he ho
  cases erasing <;> exact h

theorem consShape (erasing : Bool) (raw out d k typ head tail headOut tailOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hh : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) headOut d k head)))
    (ht : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) tailOut d k tail)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta (graph3 consConstructor out typ headOut tailOut)) := by
  have h := OriginalRawSyntaxTransportInternalFoldConsProof.consForward
    (selectedMode erasing) raw out d k typ head tail headOut tailOut hc hh ht ho
  cases erasing <;> exact h

theorem bottomUnchanged (erasing : Bool) (raw out d k typ : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw typ)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta (equal out raw)) := by
  have h := OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.bottomForward
    (selectedMode erasing) raw out d k typ hc ho
  cases erasing <;> exact h

theorem nilUnchanged (erasing : Bool) (raw out d k : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0)))
    (ho : Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode erasing)) out d k raw))) :
    Nonempty (Derivation body Delta (equal out raw)) := by
  have h := OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.nilForward
    (selectedMode erasing) raw out d k hc ho
  cases erasing <;> exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportShapeProof
