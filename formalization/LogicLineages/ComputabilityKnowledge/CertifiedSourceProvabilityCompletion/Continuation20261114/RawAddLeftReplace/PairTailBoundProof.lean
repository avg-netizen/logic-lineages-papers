module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.PairTailBoundProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryBounds HistoryBounds.SupportProof HistoryCancellation HistoryCancellation.OrderSupportProof
open HistoryCancellation.TransitivityProof HistoryCancellation.MonotonicityProof HistoryCancellation.IntervalProof
open LiteralRawMP.DispatcherSupportProof

noncomputable def weakTransLocal {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} (a b c : Term ctx)
 (h : Hilbert.Local T ctx G (weakBound a b)) (k : Hilbert.Local T ctx G (weakBound b c)) :
 Hilbert.Local T ctx G (weakBound a c) := by
 apply Classical.choice
 obtain ⟨ht⟩ := weakTrans T a b c
 exact ⟨.mp (.mp (.base ht) h) k⟩
noncomputable def separatedBound {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} (a b x y : Term ctx)
 (h : Hilbert.Local T ctx G (strictBound a b))
 (hx : Hilbert.Local T ctx G (weakBound x (ShellProof.top a)))
 (hy : Hilbert.Local T ctx G (weakBound (ShellProof.square b) y)) :
 Hilbert.Local T ctx G (weakBound x y) := by
 apply Classical.choice
 obtain ⟨hs⟩ := HistoryCancellation.SeparationProof.orderSeparation T a b
 obtain ⟨hw⟩ := ShellProof.strictToWeak T (ShellProof.top a) (ShellProof.square b)
 exact ⟨weakTransLocal x _ y hx (weakTransLocal _ _ y (.mp (.base hw) (.mp (.base hs) h)) hy)⟩

theorem sectorLL {n ctx : Nat} (p : Program n) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (strictBound b c) (.imp (HistoryOrder.lower a b) (.imp (HistoryOrder.lower a c)
  (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := strictBound b c
 let L := HistoryOrder.lower a b
 let R := HistoryOrder.lower a c
 let G := [R,L,H]
 have hbc : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 have hl : Hilbert.Local T ctx G L := .hypothesis (by simp [G])
 have hr : Hilbert.Local T ctx G R := .hypothesis List.mem_cons_self
 obtain ⟨hi⟩ := pairLowerInterval p tag hp a b
 obtain ⟨hj⟩ := pairLowerInterval p tag hp a c
 have hx := Hilbert.Local.mp (.base (.logical (.andRight _ _))) (.mp (.base hi) hl)
 have hy := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (.mp (.base hj) hr)
 have hout := separatedBound b c _ _ hbc hx hy
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem sectorUL {n ctx : Nat} (p : Program n) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (strictBound b c) (.imp (HistoryOrder.upper a b) (.imp (HistoryOrder.lower a c)
  (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := strictBound b c
 let L := HistoryOrder.upper a b
 let R := HistoryOrder.lower a c
 let G := [R,L,H]
 have hbc : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 have hl : Hilbert.Local T ctx G L := .hypothesis (by simp [G])
 have hr : Hilbert.Local T ctx G R := .hypothesis List.mem_cons_self
 obtain ⟨hi⟩ := pairUpperInterval p tag hp a b
 obtain ⟨hj⟩ := pairLowerInterval p tag hp a c
 have hx := Hilbert.Local.mp (.base (.logical (.andRight _ _))) (.mp (.base hi) hl)
 have hy := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) (.mp (.base hj) hr)
 have hout := separatedBound a c _ _ hr hx hy
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem sectorUU {n ctx : Nat} (p : Program n) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (strictBound b c) (.imp (HistoryOrder.upper a b) (.imp (HistoryOrder.upper a c)
  (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := strictBound b c
 let L := HistoryOrder.upper a b
 let R := HistoryOrder.upper a c
 let G := [R,L,H]
 have hbc : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 have hl : Hilbert.Local T ctx G L := .hypothesis (by simp [G])
 have hr : Hilbert.Local T ctx G R := .hypothesis List.mem_cons_self
 obtain ⟨hi⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag hp ctx a b
 obtain ⟨hj⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag hp ctx a c
 obtain ⟨hw⟩ := ShellProof.strictToWeak T b c
 obtain ⟨hm⟩ := weakAddLeft T b c (.add (.mul a a) a)
 have hv := Hilbert.Local.mp (.base hm) (.mp (.base hw) hbc)
 have hright := Hilbert.Local.mp (.mp (.base (HistoryBounds.PairProof.weakTransport _ _ _)) (.mp (.base hj) hr)) hv
 have hout := Hilbert.Local.mp (.mp (.base (weakChildTransport _ _ _)) (.mp (.base hi) hl)) hright
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem sectorLU {n ctx : Nat} (p : Program n) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (strictBound b c) (.imp (HistoryOrder.lower a b) (.imp (HistoryOrder.upper a c)
  (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)))))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := strictBound b c
 let L := HistoryOrder.lower a b
 let R := HistoryOrder.upper a c
 let G := [R,L,H]
 have hbc : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 have hl : Hilbert.Local T ctx G L := .hypothesis (by simp [G])
 have hr : Hilbert.Local T ctx G R := .hypothesis List.mem_cons_self
 obtain ⟨ht1⟩ := strictWeakTrans T b c a
 obtain ⟨hweak⟩ := ShellProof.strictToWeak T b a
 obtain ⟨ht2⟩ := strictWeakTrans T a b a
 obtain ⟨hne⟩ := strictIrreflexive T a
 have hba := Hilbert.Local.mp (.mp (.base ht1) hbc) hr
 have hbad := Hilbert.Local.mp (.mp (.base ht2) hl) (.mp (.base hweak) hba)
 have hout : Hilbert.Local T ctx G (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)) :=
  Hilbert.Local.explosion _ hbad (.base hne)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem strictPair {n ctx : Nat} (p : Program n) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (strictBound b c) (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := strictBound b c
 let Q := weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)
 obtain ⟨hll⟩ := sectorLL p tag hp a b c
 obtain ⟨hlu⟩ := sectorLU p tag hp a b c
 obtain ⟨hul⟩ := sectorUL p tag hp a b c
 obtain ⟨huu⟩ := sectorUU p tag hp a b c
 obtain ⟨hsb⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a b
 obtain ⟨hsc⟩ := HistoryOrder.SplitProof.additiveSplit T ctx a c
 have lowerCase : Hilbert.Local T ctx [H] (.imp (HistoryOrder.lower a b) Q) := by
  have hh : Hilbert.Local T ctx [HistoryOrder.lower a b,H] H := .hypothesis (by simp)
  have hl : Hilbert.Local T ctx [HistoryOrder.lower a b,H] (HistoryOrder.lower a b) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (.mp (.mp (.mp (.base (.logical (.orElim _ _ Q)))
   (.mp (.mp (.base hll) hh) hl)) (.mp (.mp (.base hlu) hh) hl)) (.base hsc))
 have upperCase : Hilbert.Local T ctx [H] (.imp (HistoryOrder.upper a b) Q) := by
  have hh : Hilbert.Local T ctx [HistoryOrder.upper a b,H] H := .hypothesis (by simp)
  have hl : Hilbert.Local T ctx [HistoryOrder.upper a b,H] (HistoryOrder.upper a b) := .hypothesis List.mem_cons_self
  exact Hilbert.Local.discharge (.mp (.mp (.mp (.base (.logical (.orElim _ _ Q)))
   (.mp (.mp (.base hul) hh) hl)) (.mp (.mp (.base huu) hh) hl)) (.base hsc))
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.mp (.base (.logical (.orElim _ _ Q))) lowerCase) upperCase) (.base hsb)))⟩

theorem weakPair {n ctx : Nat} (p : Program n) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (weakBound b c) (weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := weakBound (HistoryDifference.pairCall tag a b) (HistoryDifference.pairCall tag a c)
 let E := Formula.equal c b
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hcg := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := [E]) tag a c a b
  (.base (.logical (.reflexive a))) he
 have hout := Hilbert.Local.mp (.mp (.base (HistoryBounds.PairProof.weakTransport _ _ _)) hcg)
  (.base (weakReflexive (HistoryDifference.pairCall tag a b)))
 have heq : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hs⟩ := strictPair p tag hp a b c
 obtain ⟨hcases⟩ := HistoryCancellation.TrichotomyProof.weakSplit T b c
 exact ⟨Hilbert.compose (.mp (.mp (.logical (.orElim E (strictBound b c) Q)) heq) hs) hcases⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.PairTailBoundProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.PairTailBoundProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.PairTailBoundProof.weakPair
