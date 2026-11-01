module
public import LogicLineages.OrdinalComparison.RangeRangeNodeTargets
public import LogicLineages.OrdinalComparison.ComparisonNodeProgramProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionProgramProof
public import LogicLineages.OrdinalComparison.SuccessorNormalizationProgramProof
public import LogicLineages.OrdinalComparison.KernelProfileLeafProof
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

attribute [local irreducible] encodedSuccessorNormalization encodedOneVariableComparisonDomainBound
  encodedComparisonOuter encodedKernelProfileLeafTail encodedLimitPairCertificateTail

abbrev KernelTailParameters := Nat × Nat × Nat × List Nat

theorem kernel_tails_primitive : Primrec (fun p : KernelTailParameters =>
    encodedRangeRangeKernelTails p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have he : Primrec (fun p : KernelTailParameters => p.1) := Primrec.fst
  have hc : Primrec (fun p : KernelTailParameters => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : KernelTailParameters => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hprofiles : Primrec (fun p : KernelTailParameters => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hmass := KernelMassProgram.primitive.2.2.1.comp (he.pair (hc.pair hd))
  have hEta : Primrec (fun p : KernelTailParameters × Nat => p.1.1) := he.comp Primrec.fst
  have hC : Primrec (fun p : KernelTailParameters × Nat => p.1.2.1) := hc.comp Primrec.fst
  have hD : Primrec (fun p : KernelTailParameters × Nat => p.1.2.2.1) := hd.comp Primrec.fst
  have hP : Primrec (fun p : KernelTailParameters × Nat => p.2) := Primrec.snd
  have hL := LimitPairCertificate.principal_source.1.comp hEta
  have hlimit1 := LimitPairCertificate.actual_program.1.comp (hEta.pair (hP.pair (hC.pair hD)))
  have hlimit2 := LimitPairCertificate.actual_program.1.comp (hEta.pair (hP.pair (hD.pair hC)))
  have hbound1 := KernelProfileLeaf.bounded_program.1.comp (hL.pair (hP.pair hC))
  have hbound2 := KernelProfileLeaf.bounded_program.1.comp (hL.pair (hP.pair hD))
  have hlocal : Primrec₂ (fun p : KernelTailParameters => fun P : Nat =>
      [encodedLimitPairCertificateTail p.1 P p.2.1 p.2.2.1,
        encodedLimitPairCertificateTail p.1 P p.2.2.1 p.2.1,
        encodedKernelProfileLeafTail (encodedComparisonPrincipalNote p.1) P p.2.1,
        encodedKernelProfileLeafTail (encodedComparisonPrincipalNote p.1) P p.2.2.1]) :=
    Primrec.list_cons.comp hlimit1 (Primrec.list_cons.comp hlimit2
      (Primrec.list_cons.comp hbound1 (Primrec.list_cons.comp hbound2 (Primrec.const []))))
  exact Primrec.list_cons.comp hmass (Primrec.list_flatMap hprofiles hlocal)

theorem normalization_primitive : Primrec encodedRangeRangeNormalization := by
  have ha : Primrec (fun p : Nat × Nat => encodedComparisonOuter p.1) := ComparisonExpansion.outer_primitive.comp Primrec.fst
  have hb : Primrec (fun p : Nat × Nat => encodedComparisonOuter p.2) := ComparisonExpansion.outer_primitive.comp Primrec.snd
  have ht := Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)) (Primrec.const 2)
  have hhigh := Primrec.ite ht Primrec.fst Primrec.snd
  have hlow := Primrec.ite ht Primrec.snd Primrec.fst
  have hH := ComparisonExpansion.outer_primitive.comp hhigh
  have hM := ComparisonExpansion.outer_primitive.comp hlow
  exact SuccessorNormalization.primitive.2.2.comp ((ComparisonExpansion.prefix_program.1.comp hhigh).pair
    ((Primrec.fst.comp hH).pair ((Primrec.fst.comp hM).pair (Primrec.snd.comp hH))))

theorem local_tails_primitive : Primrec encodedRangeRangeLocalTails := by
  have he : Primrec (fun q : ComparisonQuery => q.1.1) := Primrec.fst.comp Primrec.fst
  have hf : Primrec (fun q : ComparisonQuery => q.1.2) := Primrec.snd.comp Primrec.fst
  have ha := ComparisonExpansion.outer_primitive.comp he
  have hb := ComparisonExpansion.outer_primitive.comp hf
  have hr := normalization_primitive.comp (Primrec.fst : Primrec (fun q : ComparisonQuery => q.1))
  have hsource := Primrec.fst.comp hr
  have hEtaLast := Primrec.fst.comp (Primrec.snd.comp hr)
  have hNlast := Primrec.snd.comp (Primrec.snd.comp hr)
  have hdomE := OneVariableComparison.source_program.1.comp he
  have hdomF := OneVariableComparison.source_program.1.comp hf
  have hdomLast := OneVariableComparison.source_program.1.comp hsource
  have hstripE := OneVariableComparison.source_program.1.comp (SourceKernelCalls.program.1.comp he)
  have hstripF := OneVariableComparison.source_program.1.comp (SourceKernelCalls.program.1.comp hf)
  have hstripLast := OneVariableComparison.source_program.1.comp (SourceKernelCalls.program.1.comp hsource)
  have hbase : Primrec (fun q : ComparisonQuery =>
      [encodedOneVariableComparisonDomainBound q.1.1,encodedOneVariableComparisonDomainBound q.1.2,
        (encodedRangeRangeNormalization q.1).2.2,encodedOneVariableComparisonDomainBound (encodedRangeRangeNormalization q.1).1,
        encodedOneVariableComparisonDomainBound (encodedComparisonStripOuter q.1.1),
        encodedOneVariableComparisonDomainBound (encodedComparisonStripOuter q.1.2),
        encodedOneVariableComparisonDomainBound (encodedComparisonStripOuter (encodedRangeRangeNormalization q.1).1)]) :=
    Primrec.list_cons.comp hdomE (Primrec.list_cons.comp hdomF (Primrec.list_cons.comp hNlast
      (Primrec.list_cons.comp hdomLast (Primrec.list_cons.comp hstripE
        (Primrec.list_cons.comp hstripF (Primrec.list_cons.comp hstripLast (Primrec.const [])))))))
  have hetas : Primrec (fun q : ComparisonQuery =>
      [(encodedComparisonOuter q.1.1).1,(encodedComparisonOuter q.1.2).1,(encodedRangeRangeNormalization q.1).2.1]) :=
    Primrec.list_cons.comp (Primrec.fst.comp ha)
      (Primrec.list_cons.comp (Primrec.fst.comp hb) (Primrec.list_cons.comp hEtaLast (Primrec.const [])))
  have hC : Primrec (fun p : ComparisonQuery × Nat => (encodedComparisonOuter p.1.1.1).2) :=
    Primrec.snd.comp (ha.comp Primrec.fst)
  have hD : Primrec (fun p : ComparisonQuery × Nat => (encodedComparisonOuter p.1.1.2).2) :=
    Primrec.snd.comp (hb.comp Primrec.fst)
  have hl : Primrec (fun p : ComparisonQuery × Nat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hp : Primrec (fun p : ComparisonQuery × Nat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hprofiles := Primrec.list_cons.comp hl (Primrec.list_cons.comp hp
    (Primrec.list_cons.comp (Primrec.const 1) (Primrec.const [])))
  have hlocal : Primrec₂ (fun q : ComparisonQuery => fun eta : Nat => encodedRangeRangeKernelTails eta
      (encodedComparisonOuter q.1.1).2 (encodedComparisonOuter q.1.2).2 [q.2.1,q.2.2,1]) :=
    kernel_tails_primitive.comp (Primrec.snd.pair (hC.pair (hD.pair hprofiles)))
  exact Primrec.list_append.comp hbase (Primrec.list_flatMap hetas hlocal)

theorem local_tail_primitive : Primrec encodedRangeRangeLocalTail := by
  have hmax : Primrec (fun values : List Nat => values.foldr max 1) :=
    Primrec.list_foldr Primrec.id (Primrec.const 1)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hmax.comp local_tails_primitive

theorem program : Targets.ActualRangeRangeQueryNodeProgram := by
  have he : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hf : Primrec (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hN := Primrec.nat_max.comp (ComparisonNode.table_tail_primitive.comp Primrec.snd) (local_tail_primitive.comp Primrec.fst)
  have hsign := ComparisonNode.point_program.2.1.comp (he.to_comp.pair (hf.to_comp.pair hN.to_comp))
  exact ⟨local_tail_primitive,hsign.pair hN.to_comp⟩

end LogicLineages.OrdinalComparison.RangeRangeNode
