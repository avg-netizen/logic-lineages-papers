module
public import LogicLineages.OrdinalComparison.RangePositiveNodeTargets
public import LogicLineages.OrdinalComparison.ComparisonNodeProgramProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionProgramProof
public import LogicLineages.OrdinalComparison.CollectedRangeBandProof
public import LogicLineages.OrdinalComparison.RangeAffineProgramProof
public import LogicLineages.OrdinalComparison.AffineProfileCertificateProof
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

attribute [local irreducible] encodedCollectedNormalize encodedPositiveZeroBound encodedOneVariableComparisonValue

theorem local_tail_computable : Computable (fun p : Nat × Nat × Nat =>
    encodedRangePositiveLocalTail p.1 p.2.1 p.2.2) := by
  have hsource : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hpos : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hprofile : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hform := encodedCollectedNormalizeComputable.comp hpos.to_comp
  have hc := Computable.fst.comp (Primrec.unpair.to_comp.comp hform)
  have ha := Computable.fst.comp (Primrec.unpair.to_comp.comp (Computable.snd.comp (Primrec.unpair.to_comp.comp hform)))
  have houter := ComparisonExpansion.outer_primitive.comp hsource
  have hL := LimitPairCertificate.principal_source.1.comp (Primrec.fst.comp houter)
  have hmass := Primrec.snd.comp houter
  have hdom := OneVariableComparison.source_program.1.comp hsource
  have hband := collectedRangeThresholdCode.1.to_comp.comp hform
  have haff := RangeAffineProgram.actual_program.1.to_comp.comp (hsource.to_comp.pair (ha.pair hc))
  have hgap := AffineProfileCertificate.actual_program.1.to_comp.comp
    (hL.to_comp.pair (hprofile.to_comp.pair (hmass.to_comp.pair (ha.pair hc))))
  exact Primrec.nat_max.to_comp.comp hdom.to_comp
    (Primrec.nat_max.to_comp.comp hband (Primrec.nat_max.to_comp.comp haff hgap))

theorem program : Targets.ActualRangePositiveQueryNodeProgram := by
  have he : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hf : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hleft : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hright : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hpositiveLeft := Primrec.eq.comp (Primrec.nat_mod.comp he (Primrec.const 2)) (Primrec.const 0)
  have hsource := Primrec.ite hpositiveLeft hf he
  have hpositive := Primrec.ite hpositiveLeft
    (Primrec.nat_div.comp he (Primrec.const 2)) (Primrec.nat_div.comp hf (Primrec.const 2))
  have hprofile := Primrec.ite hpositiveLeft hright hleft
  have hcut := local_tail_computable.comp (hsource.to_comp.pair (hpositive.to_comp.pair hprofile.to_comp))
  have hN := Primrec.nat_max.to_comp.comp (ComparisonNode.table_tail_primitive.comp Primrec.snd).to_comp hcut
  have hsign := ComparisonNode.point_program.2.1.comp (he.to_comp.pair (hf.to_comp.pair hN))
  exact ⟨local_tail_computable,hsign.pair hN⟩

end LogicLineages.OrdinalComparison.RangePositiveNode
