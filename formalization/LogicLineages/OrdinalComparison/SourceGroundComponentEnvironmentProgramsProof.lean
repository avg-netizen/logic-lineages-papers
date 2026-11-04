module
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment.Proof
attribute [local irreducible] Nat.unpair Nat.sqrt

private theorem bound_primitive : Primrec bound := by
  have hmap : Primrec (fun n : Nat => (List.range n).map (fun j => Nat.pair j 0)) :=
    Primrec.list_map Primrec.list_range
      (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0)).to₂
  have hmax : Primrec (fun n : Nat =>
      ((List.range n).map (fun j => Nat.pair j 0)).foldr max 0) :=
    Primrec.list_foldr hmap (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.nat_add.comp (Primrec.const 1) hmax

private theorem slot_primitive : Primrec (fun p : List Nat × Nat => slot p.1 p.2) := by
  have hunpair := Primrec.unpair.comp (Primrec.snd (α := List Nat) (β := Nat))
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hunpair) (Primrec.const 0))
    ((Primrec.list_getD 0).comp Primrec.fst (Primrec.fst.comp hunpair)) (Primrec.const 0)

/-- The finite component-code layout and its lookups are primitive recursive. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  refine ⟨bound_primitive,slot_primitive,?_⟩
  exact Primrec.list_map
    (Primrec.list_range.comp (bound_primitive.comp Primrec.list_length)) slot_primitive.to₂
end LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment.Proof
