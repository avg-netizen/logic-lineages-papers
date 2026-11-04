module
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceTargets
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Proof

theorem advance_primitive : Primrec advance := by
  have hd : Primrec (fun s : TraceState => s.1/2) := Primrec.nat_div.comp Primrec.fst (Primrec.const 2)
  have hm : Primrec (fun s : TraceState => s.1%2) := Primrec.nat_mod.comp Primrec.fst (Primrec.const 2)
  exact Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.const 2)) Primrec.id
    (hd.pair (Primrec.list_cons.comp hm Primrec.snd))

theorem trace_primitive : Primrec trace :=
  Primrec.nat_iterate Primrec.id (Primrec.id.pair (Primrec.const [])) (advance_primitive.comp Primrec.snd).to₂

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := ⟨advance_primitive,trace_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace.Proof
