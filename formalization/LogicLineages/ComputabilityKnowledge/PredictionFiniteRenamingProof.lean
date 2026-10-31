module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingProof
open Turing PredictionFiniteRenaming PredictionFiniteRenamingTargets

theorem effectiveNumericMaps : EffectiveNumericMaps := by
  intro α _ _ _
  have hi : Primrec (items : List α → List α) :=
    Primrec.list_cons.comp (Primrec.const default) Primrec.id
  constructor
  · exact Primrec.nat_mod.comp
      (Primrec.list_idxOf.comp Primrec.snd (hi.comp Primrec.fst))
      (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1))
  · exact Primrec.list_getI.comp (hi.comp Primrec.fst)
      (Primrec.nat_mod.comp Primrec.snd
        (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1)))

theorem inverseOnEnumeration : InverseOnEnumeration := by
  intro α _ _ tail x hx
  have hlt : (items tail).idxOf x < tail.length + 1 := by
    simpa [items] using (List.idxOf_lt_length_iff.mpr hx)
  simp [decode, encode, index, Nat.mod_eq_of_lt hlt]

theorem exactRenamedStep : ExactRenamedStep := by
  intro Γ Λ _ _ _ _ m states alphabet ha c hc
  exact TM0.Machine.map_step m (toFinite alphabet) (fromFinite alphabet)
    (toFinite states) (fromFinite states)
    (fun a => inverseOnEnumeration Γ alphabet a (ha a))
    (fun q hq => inverseOnEnumeration Λ states q hq) c hc

theorem exactSupportedSimulation : ExactSupportedSimulation := by
  intro Γ Λ _ _ _ _ m states alphabet hm ha
  exact TM0.Machine.map_respects m (toFinite alphabet) (fromFinite alphabet)
    (toFinite states) (fromFinite states) hm
    (fun a => inverseOnEnumeration Γ alphabet a (ha a))
    (fun q hq => inverseOnEnumeration Λ states q hq)

end LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingProof
