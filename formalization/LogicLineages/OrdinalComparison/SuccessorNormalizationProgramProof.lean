module
public import LogicLineages.OrdinalComparison.SuccessorNormalizationTargets
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramProof
public import LogicLineages.OrdinalComparison.SuccessorWordProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SuccessorNormalization

private theorem step_primitive : Primrec (fun p : Nat × Nat × SuccessorNormalizationState =>
    encodedSuccessorNormalizationStep p.1 p.2.1 p.2.2) := by
  have hl : Primrec (fun p : Nat × Nat × SuccessorNormalizationState => p.1) := Primrec.fst
  have hc : Primrec (fun p : Nat × Nat × SuccessorNormalizationState => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Nat × Nat × SuccessorNormalizationState => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn := Primrec.fst.comp hs
  have he := Primrec.fst.comp (Primrec.snd.comp hs)
  have ht := Primrec.snd.comp (Primrec.snd.comp hs)
  have hactive := (Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp he hl) (Primrec.const 2)).and
    (Primrec.nat_lt.comp (Primrec.const 0) (OrdinalSuccessorProgram.primitive.1.comp he))
  have hpred := OrdinalSuccessorProgram.primitive.2.comp he
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp hpred
  have hmass := Primrec.nat_add.comp (Primrec.succ.comp hc) hnorm
  have hprefix := SuccessorWordProgram.primitive.1.comp (hn.pair (he.pair hmass))
  have hfull := SuccessorWordProgram.primitive.1.comp (hprefix.pair (hpred.pair hc))
  exact Primrec.ite hactive
    (hprefix.pair (hpred.pair (Primrec.nat_max.comp ht (OneVariableComparison.source_program.1.comp hfull)))) hs

private theorem trace_primitive : Primrec (fun p : Nat × Nat × Nat × Nat × Nat =>
    encodedSuccessorNormalizationTrace p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let A := Nat × Nat × Nat × Nat × Nat
  have hn : Primrec (fun p : A => p.1) := Primrec.fst
  have he : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : A => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hk : Primrec (fun p : A => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hfull := SuccessorWordProgram.primitive.1.comp (hn.pair (he.pair hc))
  have hinit : Primrec (fun p : A => encodedSuccessorNormalizationInitial p.1 p.2.1 p.2.2.2.1) :=
    hn.pair (he.pair (Primrec.nat_max.comp (Primrec.const 1) (OneVariableComparison.source_program.1.comp hfull)))
  have hstep : Primrec₂ (fun p : A => fun s : SuccessorNormalizationState =>
      encodedSuccessorNormalizationStep p.2.2.1 p.2.2.2.1 s) :=
    step_primitive.comp ((hl.comp Primrec.fst).pair ((hc.comp Primrec.fst).pair Primrec.snd))
  exact Primrec.nat_iterate hk hinit hstep

theorem primitive : Targets.SuccessorNormalizationProgramsPrimitiveRecursive := by
  refine ⟨step_primitive,trace_primitive,?_⟩
  let A := Nat × Nat × Nat × Nat
  have hn : Primrec (fun p : A => p.1) := Primrec.fst
  have he : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp he
  have htrace := trace_primitive.comp (hn.pair (he.pair (hl.pair (hc.pair hnorm))))
  have hprefix := Primrec.fst.comp htrace
  have hlast := Primrec.fst.comp (Primrec.snd.comp htrace)
  have htail := Primrec.snd.comp (Primrec.snd.comp htrace)
  exact (SuccessorWordProgram.primitive.1.comp (hprefix.pair (hlast.pair hc))).pair (hlast.pair htail)

end LogicLineages.OrdinalComparison.SuccessorNormalization
