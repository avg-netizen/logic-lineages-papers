module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.OffsetProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SectorProof
open GorbowSyntax GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof ShellProof

theorem lowerLower {arity : Nat} (p : GorbowPRProgram.Program arity) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b c d : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.lower a b) (.imp (HistoryOrder.lower c d)
        (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c d))
          (.conj (.equal a c) (.equal b d)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let L := HistoryOrder.lower a b
  let R := HistoryOrder.lower c d
  let x := HistoryDifference.pairCall tag a b
  let y := HistoryDifference.pairCall tag c d
  let E := Formula.equal x y
  obtain ⟨hil⟩ := IntervalProof.pairLowerInterval p tag ht a b
  obtain ⟨hir⟩ := IntervalProof.pairLowerInterval p tag ht c d
  obtain ⟨hvl⟩ := HistoryOrder.PairProof.pairLowerOrder arity p tag ht ctx a b
  obtain ⟨hvr⟩ := HistoryOrder.PairProof.pairLowerOrder arity p tag ht ctx c d
  obtain ⟨hmj⟩ := SeparationProof.sameMajor T b d x y
  have hl : Hilbert.Local T ctx [E,R,L] L := .hypothesis (by simp)
  have hr : Hilbert.Local T ctx [E,R,L] R := .hypothesis (by simp)
  have he : Hilbert.Local T ctx [E,R,L] E := .hypothesis List.mem_cons_self
  have il := Hilbert.Local.mp (.base hil) hl
  have ir := Hilbert.Local.mp (.base hir) hr
  have lf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) il
  have lu := Hilbert.Local.mp (.base (.logical (.andRight _ _))) il
  have rf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ir
  have ru := Hilbert.Local.mp (.base (.logical (.andRight _ _))) ir
  have hm : Hilbert.Local T ctx [E,R,L] (.equal b d) :=
    .mp (.mp (.mp (.mp (.mp (.base hmj) lf) lu) rf) ru) he
  have vl := Hilbert.Local.mp (.base hvl) hl
  have vr := Hilbert.Local.mp (.base hvr) hr
  have hv := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ vl) (localTrans _ _ _ he vr)
  have hf := OffsetProof.lowerSame a b c d hm hv
  have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hf) hm
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.discharge hout)))⟩

theorem upperUpper {arity : Nat} (p : GorbowPRProgram.Program arity) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b c d : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.upper a b) (.imp (HistoryOrder.upper c d)
        (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c d))
          (.conj (.equal a c) (.equal b d)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let L := HistoryOrder.upper a b
  let R := HistoryOrder.upper c d
  let x := HistoryDifference.pairCall tag a b
  let y := HistoryDifference.pairCall tag c d
  let E := Formula.equal x y
  obtain ⟨hil⟩ := IntervalProof.pairUpperInterval p tag ht a b
  obtain ⟨hir⟩ := IntervalProof.pairUpperInterval p tag ht c d
  obtain ⟨hvl⟩ := HistoryOrder.PairProof.pairUpperOrder arity p tag ht ctx a b
  obtain ⟨hvr⟩ := HistoryOrder.PairProof.pairUpperOrder arity p tag ht ctx c d
  obtain ⟨hmj⟩ := SeparationProof.sameMajor T a c x y
  have hl : Hilbert.Local T ctx [E,R,L] L := .hypothesis (by simp)
  have hr : Hilbert.Local T ctx [E,R,L] R := .hypothesis (by simp)
  have he : Hilbert.Local T ctx [E,R,L] E := .hypothesis List.mem_cons_self
  have il := Hilbert.Local.mp (.base hil) hl
  have ir := Hilbert.Local.mp (.base hir) hr
  have lf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) il
  have lu := Hilbert.Local.mp (.base (.logical (.andRight _ _))) il
  have rf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ir
  have ru := Hilbert.Local.mp (.base (.logical (.andRight _ _))) ir
  have hm : Hilbert.Local T ctx [E,R,L] (.equal a c) :=
    .mp (.mp (.mp (.mp (.mp (.base hmj) lf) lu) rf) ru) he
  have vl := Hilbert.Local.mp (.base hvl) hl
  have vr := Hilbert.Local.mp (.base hvr) hr
  have hv := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ vl) (localTrans _ _ _ he vr)
  have hs := OffsetProof.upperSame a b c d hm hv
  have hout := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hm) hs
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.discharge hout)))⟩

theorem lowerUpper {arity : Nat} (p : GorbowPRProgram.Program arity) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b c d : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.lower a b) (.imp (HistoryOrder.upper c d)
        (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c d))
          (.conj (.equal a c) (.equal b d)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let L := HistoryOrder.lower a b
  let R := HistoryOrder.upper c d
  let x := HistoryDifference.pairCall tag a b
  let y := HistoryDifference.pairCall tag c d
  let E := Formula.equal x y
  obtain ⟨hil⟩ := IntervalProof.pairLowerInterval p tag ht a b
  obtain ⟨hir⟩ := IntervalProof.pairUpperInterval p tag ht c d
  obtain ⟨hvl⟩ := HistoryOrder.PairProof.pairLowerOrder arity p tag ht ctx a b
  obtain ⟨hvr⟩ := HistoryOrder.PairProof.pairUpperOrder arity p tag ht ctx c d
  obtain ⟨hmj⟩ := SeparationProof.sameMajor T b c x y
  have hl : Hilbert.Local T ctx [E,R,L] L := .hypothesis (by simp)
  have hr : Hilbert.Local T ctx [E,R,L] R := .hypothesis (by simp)
  have he : Hilbert.Local T ctx [E,R,L] E := .hypothesis List.mem_cons_self
  have il := Hilbert.Local.mp (.base hil) hl
  have ir := Hilbert.Local.mp (.base hir) hr
  have lf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) il
  have lu := Hilbert.Local.mp (.base (.logical (.andRight _ _))) il
  have rf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ir
  have ru := Hilbert.Local.mp (.base (.logical (.andRight _ _))) ir
  have hm : Hilbert.Local T ctx [E,R,L] (.equal b c) :=
    .mp (.mp (.mp (.mp (.mp (.base hmj) lf) lu) rf) ru) he
  have vl := Hilbert.Local.mp (.base hvl) hl
  have vr := Hilbert.Local.mp (.base hvr) hr
  have hv := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ vl) (localTrans _ _ _ he vr)
  obtain ⟨ht⟩ := TransitivityProof.strictWeakTrans T a b a
  obtain ⟨hn⟩ := OrderSupportProof.strictIrreflexive T a
  have hw := OffsetProof.crossOffset a b c d hm hv
  have hloop := Hilbert.Local.mp (.mp (.base ht) hl) hw
  have hout := Hilbert.Local.explosion (.conj (.equal a c) (.equal b d)) hloop (.base hn)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.discharge hout)))⟩

theorem upperLower {arity : Nat} (p : GorbowPRProgram.Program arity) tag
    (ht : (GorbowPRRegistry.nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩)
    {ctx : Nat} (a b c d : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.upper a b) (.imp (HistoryOrder.lower c d)
        (.imp (.equal (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag c d))
          (.conj (.equal a c) (.equal b d)))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let L := HistoryOrder.upper a b
  let R := HistoryOrder.lower c d
  let x := HistoryDifference.pairCall tag a b
  let y := HistoryDifference.pairCall tag c d
  let E := Formula.equal x y
  obtain ⟨hil⟩ := IntervalProof.pairUpperInterval p tag ht a b
  obtain ⟨hir⟩ := IntervalProof.pairLowerInterval p tag ht c d
  obtain ⟨hvl⟩ := HistoryOrder.PairProof.pairUpperOrder arity p tag ht ctx a b
  obtain ⟨hvr⟩ := HistoryOrder.PairProof.pairLowerOrder arity p tag ht ctx c d
  obtain ⟨hmj⟩ := SeparationProof.sameMajor T a d x y
  have hl : Hilbert.Local T ctx [E,R,L] L := .hypothesis (by simp)
  have hr : Hilbert.Local T ctx [E,R,L] R := .hypothesis (by simp)
  have he : Hilbert.Local T ctx [E,R,L] E := .hypothesis List.mem_cons_self
  have il := Hilbert.Local.mp (.base hil) hl
  have ir := Hilbert.Local.mp (.base hir) hr
  have lf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) il
  have lu := Hilbert.Local.mp (.base (.logical (.andRight _ _))) il
  have rf := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ir
  have ru := Hilbert.Local.mp (.base (.logical (.andRight _ _))) ir
  have hm : Hilbert.Local T ctx [E,R,L] (.equal a d) :=
    .mp (.mp (.mp (.mp (.mp (.base hmj) lf) lu) rf) ru) he
  have vl := Hilbert.Local.mp (.base hvl) hl
  have vr := Hilbert.Local.mp (.base hvr) hr
  have hv := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ vl) (localTrans _ _ _ he vr)
  obtain ⟨ht⟩ := TransitivityProof.strictWeakTrans T c d c
  obtain ⟨hn⟩ := OrderSupportProof.strictIrreflexive T c
  have hw := OffsetProof.crossOffset c d a b (HistoryOrder.StepProof.localSym _ _ hm) (HistoryOrder.StepProof.localSym _ _ hv)
  have hloop := Hilbert.Local.mp (.mp (.base ht) hr) hw
  have hout := Hilbert.Local.explosion (.conj (.equal a c) (.equal b d)) hloop (.base hn)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.discharge hout)))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.SectorProof
