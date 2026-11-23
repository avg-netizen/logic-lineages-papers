module
public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecTargets
open NumberedWindowDirectAlgorithm (Entry Witness readEntry readWitness)
open NumberedWindowFieldAlgorithm (pack packNode)

def packedRow (e : Entry) : Nat :=
  packNode 4 [e.1, e.2.1, e.2.2]

def packedWitness (w : Witness) : Nat :=
  packNode 5 [pack w.1, pack w.2.1, pack (w.2.2.map packedRow)]

def ExactPackedRow : Prop :=
  ∀ e, readEntry (packedRow e) = some e

def ExactPackedWitness : Prop :=
  ∀ w, readWitness (packedWitness w) = some w

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecTargets
