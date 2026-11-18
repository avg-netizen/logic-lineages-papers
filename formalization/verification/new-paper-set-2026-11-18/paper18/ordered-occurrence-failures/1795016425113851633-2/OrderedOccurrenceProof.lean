module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceSupportProof
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRawCalibrationProof
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRawPrograms
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof

theorem programs : OrderedOccurrenceTargets.Programs :=
  ⟨fun q => OrderedOccurrenceRaw.dispatch q.1 q.2,
    OrderedOccurrenceRaw.dispatch_computable,OrderedOccurrenceRaw.dispatch_calibration⟩

theorem full : OrderedOccurrenceTargets.Full :=
  ⟨exactRoster,exactLive,exactInactive,orderedCoverage,maximumCoverage,tieReduction,
    fullCoverage,continuationProvenance,freeSupport,programs⟩
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
