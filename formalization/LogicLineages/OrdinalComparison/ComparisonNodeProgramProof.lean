module
public import LogicLineages.OrdinalComparison.ComparisonNodeTargets
public import LogicLineages.OrdinalComparison.OneVariableComparisonProgramProof
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosProof
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode

attribute [local irreducible] encodedCollectedNormalize encodedPositiveZeroBound encodedOneVariableComparisonValue

theorem natural_sign (a b : Nat) : comparisonNaturalSign a b≤2 ∧
    (comparisonNaturalSign a b=0 ↔ a<b) ∧ (comparisonNaturalSign a b=1 ↔ a=b) ∧
    (comparisonNaturalSign a b=2 ↔ b<a) := by
  by_cases hab : a<b
  · have hba : ¬b<a := not_lt_of_ge hab.le
    simp [comparisonNaturalSign,hab,hba,ne_of_lt hab]
  · by_cases hba : b<a
    · simp [comparisonNaturalSign,hab,hba,Ne.symm (ne_of_lt hba)]
    · have heq : a=b := by omega
      subst b
      simp [comparisonNaturalSign]

theorem point_program : Targets.ActualSourcePairPointSignProgram := by
  have hn : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hsign : Primrec₂ comparisonNaturalSign :=
    Primrec.ite Primrec.nat_lt (Primrec.const 0)
      (Primrec.ite (Primrec.nat_lt.comp Primrec.snd Primrec.fst) (Primrec.const 2) (Primrec.const 1))
  have hp : Computable (fun p : Nat × Nat × Nat => encodedSourcePairSignAt p.1 p.2.1 p.2.2) :=
    hsign.to_comp.comp (OneVariableComparison.source_program.2.1.comp hn.to_comp hx.to_comp)
      (OneVariableComparison.source_program.2.1.comp hm.to_comp hx.to_comp)
  refine ⟨hsign,hp,?_⟩
  intro E F hE hF x hxE hxF
  dsimp only
  unfold encodedSourcePairSignAt
  rw [((OneVariableComparison.source_program.2.2 E hE).2.2 x hxE).2,
    ((OneVariableComparison.source_program.2.2 F hF).2.2 x hxF).2]
  exact natural_sign _ _

theorem table_tail_primitive : Primrec encodedComparisonTableTail := by
  have hm : Primrec (fun table : ComparisonNodeTable => table.map (fun p => p.2.2)) :=
    Primrec.list_map Primrec.id (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hmax : Primrec (fun values : List Nat => values.foldr max 1) :=
    Primrec.list_foldr Primrec.id (Primrec.const 1)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hmax.comp hm

theorem local_tail_computable : Computable₂ encodedPositiveNodeLocalTail := by
  have he : Computable (fun p : Nat × Nat => (encodedCollectedNormalize p.1).unpair.1) :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp (encodedCollectedNormalizeComputable.comp Computable.fst))
  have hf : Computable (fun p : Nat × Nat => (encodedCollectedNormalize p.2).unpair.1) :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp (encodedCollectedNormalizeComputable.comp Computable.snd))
  exact Primrec.nat_max.to_comp.comp fullActualPositiveFiniteZeros.1
    (Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp he hf))

theorem positive_node_program : Targets.ActualPositiveQueryNodeProgram := by
  have he : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hf : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hde := Primrec.nat_div.comp he (Primrec.const 2)
  have hdf := Primrec.nat_div.comp hf (Primrec.const 2)
  have hbound := Primrec.nat_max.to_comp.comp (table_tail_primitive.comp Primrec.snd).to_comp
    (local_tail_computable.comp hde.to_comp hdf.to_comp)
  have hsign := point_program.2.1.comp (he.to_comp.pair (hf.to_comp.pair hbound))
  exact ⟨table_tail_primitive,local_tail_computable,hsign.pair hbound⟩

end LogicLineages.OrdinalComparison.ComparisonNode
