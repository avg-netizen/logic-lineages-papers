module
public import LogicLineages.PermittedControl.ArbitraryHeadSharedWireTargets
import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseNormalizationProof
import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseSemanticProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadSharedWire
open OrdinalComparison

private theorem normalDecoded (a : NONote) : ONote.NF (rawNoteDecode (headCode a)) := by
  rw [headCode,rawNoteDecodeEncode]
  exact a.2

theorem exactTypedWireTransport : ExactTypedWireTransport := by
  constructor
  · intro a u infinite
    let q := ArbitraryFixedHeadCollapse.transported (headCode a,u)
    have actual := ArbitraryFixedHeadCollapse.actualNormalization (headCode a,u) (normalDecoded a)
    have nonfinite : Ordinal.omega0 ≤ (rawNoteDecode (headCode a)).repr := by
      apply le_of_not_gt
      intro h
      have contrary := actual.1.mpr h
      change encodedFiniteTest (headCode a) = true at contrary
      rw [infinite] at contrary
      cases contrary
    obtain ⟨hd,part,tail,arg,state⟩ := actual.2.2 nonfinite
    change FixedHeadCollapseGraph.domain q at hd
    let lam : NONote := ⟨rawNoteDecode q.1,hd.1⟩
    have decoded : rawNoteDecode (headCode a) = a.1 := rawNoteDecodeEncode a.1
    rw [decoded] at part tail arg state
    refine ⟨lam,?_,hd.2.1,hd,part,tail,arg,state⟩
    exact rawNoteEncodeDecode (limitCode a)
  · intro f B selected a source output ν
    have checked := (ArbitraryFixedHeadCollapse.actualGraph f B selected
      (headCode a,ν source)).2 (ν output)
    have decoded : rawNoteDecode (headCode a) = a.1 := rawNoteDecodeEncode a.1
    change (originalGraph f a source output ν ↔
      ONote.NF (rawNoteDecode (headCode a)) ∧
        ν output = ParametricActualCollapse.collapseWith f
          ((rawNoteDecode (headCode a)).repr + (ν source : Ordinal))) at checked
    exact checked.trans ⟨fun h => by simpa only [decoded] using h.2,
      fun h => ⟨normalDecoded a,by simpa only [decoded] using h⟩⟩

end LogicLineages.PermittedControl.ArbitraryHeadSharedWire
