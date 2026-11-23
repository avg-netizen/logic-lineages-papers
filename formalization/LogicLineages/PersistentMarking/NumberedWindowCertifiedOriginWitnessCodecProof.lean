module
public import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecProof
open NumberedWindowDirectAlgorithm (Entry readEntry entries readWitness)
open NumberedWindowAtomicRawStepFieldProof (unpackPacked nodePacked)
open NumberedWindowCertifiedOriginWitnessCodecTargets
  (packedRow packedWitness ExactPackedRow ExactPackedWitness)

theorem packedRowView (e : Entry) : readEntry (packedRow e) = some e := by
  rcases e with ⟨target, dom, cert⟩
  unfold packedRow readEntry
  rw [nodePacked] <;> rfl

private theorem packedRows (rows : List Entry) :
    entries (rows.map packedRow) = some rows := by
  induction rows with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, entries, packedRowView, ih] <;> rfl

theorem exact_PackedWitness : ExactPackedWitness := by
  rintro ⟨kept, removed, rows⟩
  unfold packedWitness readWitness
  rw [nodePacked]
  change (do
    let k ← NumberedWindowFieldAlgorithm.unpack (NumberedWindowFieldAlgorithm.pack kept)
    let r ← NumberedWindowFieldAlgorithm.unpack (NumberedWindowFieldAlgorithm.pack removed)
    let a ← NumberedWindowFieldAlgorithm.unpack (NumberedWindowFieldAlgorithm.pack (rows.map packedRow))
    let es ← entries a
    pure (k, r, es)) = some (kept, removed, rows)
  simp only [unpackPacked]
  change (do
    let es ← entries (rows.map packedRow)
    pure (kept, removed, es)) = some (kept, removed, rows)
  rw [packedRows] <;> rfl

theorem exact_PackedRow : ExactPackedRow := packedRowView

#print axioms exact_PackedRow
#print axioms exact_PackedWitness

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecProof
