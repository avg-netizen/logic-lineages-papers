module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
open Source

/-- The local Denumerable structure has definitionally the ORIGINAL Encodable
field: ofEquiv Nat for Ty, followed by the existing List and product codecs.
No exported instance or checker definition is changed. -/
theorem actualObjectCodec : JointGammaDomainTargets.ActualObjectCodec := by
  letI : Denumerable Ty := Denumerable.ofEquiv Nat NumberedTypeCodecPrimrec.typeEquiv
  have htotal : ∀ code : Nat, ∃ obj : ContextUniform.Object,
      Encodable.decode code = some obj := by
    intro code
    exact ⟨Denumerable.ofNat ContextUniform.Object code,
      Denumerable.decode_eq_ofNat ContextUniform.Object code⟩
  have hinv : ∀ (code : Nat) (obj : ContextUniform.Object),
      Encodable.decode code = some obj ↔ ContextUniform.objectCode obj.1 obj.2 = code := by
    intro code obj
    constructor
    · intro h
      have he := Denumerable.ofNat_of_decode h
      have hk := Denumerable.encode_ofNat (α := ContextUniform.Object) code
      rw [he] at hk
      exact hk
    · intro h
      rw [← h]
      exact Encodable.encodek obj
  refine ⟨htotal,hinv,?_⟩
  intro code
  obtain ⟨obj,hd⟩ := htotal code
  rw [hd]
  exact Encodable.decode₂_eq_some.mpr ((hinv code obj).mp hd)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
