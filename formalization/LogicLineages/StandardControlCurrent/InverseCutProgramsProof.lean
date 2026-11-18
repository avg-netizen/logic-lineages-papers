module
public import LogicLineages.StandardControlCurrent.InverseCutProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutProof
open OrdinalComparison LayeredComparison.SnyatkovInverse InverseCut

theorem lowerProgram (g inv : Nat → Nat) (hi : Primrec inv) : Primrec (lowerIndex g inv) :=
  Primrec.ite (Primrec.nat_le.comp Primrec.id (Primrec.const (g 0))) (Primrec.const 0)
    (Primrec.nat_add.comp (hi.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))) (Primrec.const 1))

theorem residueProgram : Primrec (fun p : Nat × Nat × Nat => residueNext p.1 p.2.1 p.2.2) := by
  have ha : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hm : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.nat_add.comp ha (Primrec.nat_mod.comp
    (Primrec.nat_sub.comp (Primrec.nat_add.comp hr hm) (Primrec.nat_mod.comp ha hm)) hm)

theorem candidateProgram (g inv : Nat → Nat) (hi : Primrec inv) : Primrec (candidate g inv) := by
  have hlo : Primrec (fun p : Input => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun p : Input => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hr : Primrec (fun p : Input => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact residueProgram.comp ((Primrec.nat_max.comp Primrec.fst ((lowerProgram g inv hi).comp hlo)).pair (hm.pair hr))

theorem answerProgram (g inv : Nat → Nat) (hg : Primrec g) (hi : Primrec inv) : Primrec (answer g inv) := by
  have hb : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have hhigh : Primrec (fun p : Input => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec (fun p : Input => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hr : Primrec (fun p : Input => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc := candidateProgram g inv hi
  exact ((Primrec.nat_lt.comp (Primrec.const 0) hm).and
    ((Primrec.nat_lt.comp hr hm).and
      ((Primrec.nat_le.comp hc hb).and (Primrec.nat_le.comp (hg.comp hc) hhigh)))).decide

theorem full : InverseCutTargets.Full := by
  have hp := Proof.actualPrimitiveRecursion.1
  have hh := Proof.actualPrimitiveRecursion.2.1
  exact ⟨lowerCuts,leastResidue,elimination,
    lowerProgram _ _ hp,lowerProgram _ _ hh,residueProgram,
    candidateProgram _ _ hp,candidateProgram _ _ hh,
    answerProgram _ _ Phi_primrec hp,
    answerProgram _ _ FixedSeedControlResidue.Proof.H_primitive hh⟩
end LogicLineages.StandardControlCurrent.InverseCutProof
