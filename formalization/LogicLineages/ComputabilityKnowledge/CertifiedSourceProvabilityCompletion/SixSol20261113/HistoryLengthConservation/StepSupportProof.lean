module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.NilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StepSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice SupportProof

noncomputable def contraposition {T : Sentence → Prop} {ctx : Nat} (P Q : Formula ctx) :
    Derivation T (.imp (.imp P Q) (.imp (.neg Q) (.neg P))) := by
  have hp : Hilbert.Local T ctx [.neg (.neg P),.neg Q,.imp P Q] P :=
    .mp (.base (Hilbert.doubleNegation P)) (.hypothesis List.mem_cons_self)
  have hq : Hilbert.Local T ctx [.neg (.neg P),.neg Q,.imp P Q] Q :=
    .mp (.hypothesis (by simp)) hp
  have hnq : Hilbert.Local T ctx [.neg (.neg P),.neg Q,.imp P Q] (.neg Q) := .hypothesis (by simp)
  exact Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
    (Hilbert.Local.classical (.neg P) (Hilbert.Local.explosion (.neg P) hq hnq))))

noncomputable def optionCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    (itag ptag : Nat) (count a b lines index fuel : Term ctx) (h : Hilbert.Local T ctx G (.equal a b)) :
    Hilbert.Local T ctx G (.equal (run itag ptag count a lines index fuel) (run itag ptag count b lines index fuel)) :=
  StationaryProof.iterationState itag count _ _ index fuel
    (HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag a lines b lines h (.base (.logical (.reflexive lines))))

theorem newHistoryLength {n ctx : Nat} (p : Program n) (ktag ltag : Nat) (v l a : Program 1) (x : Program 3)
    (hk : (nodes p)[ktag]? = some ⟨3,HistoryKernel.kernel v l a x⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩) (history line : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (lengthCall ltag (HistoryKernel.EntryProof.newHistory (HistoryKernel.TransitionEquationsProof.someTag ktag v l a x) history line))
        (.succ (lengthCall ltag history)))) := by
  obtain ⟨_,_,_,_,hc⟩ := HistoryKernel.OptionProof.kernelNodes p ktag v l a x hk
  exact HistoryLengthOffset.ConsProof.internalLengthCons n p ltag _ hl hc ctx _ history

theorem noneCons {n ctx : Nat} (p : Program n) (itag ltag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag ptag tail index fuel)
        (noneRelation itag ltag ptag (HistoryLookup.consCall ctag line tail) out index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := HistoryLookup.consCall ctag line tail
  let P := property itag ltag ptag tail index fuel
  let E := Formula.equal (run itag ptag (lengthCall ltag code) .zero code index fuel) (state ptag (.succ out) .zero)
  let F := Formula.equal (run itag ptag (lengthCall ltag tail) .zero tail index fuel) (state ptag (.succ out) .zero)
  obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx line tail
  obtain ⟨hs⟩ := ConsRunProof.noneCons p itag ptag ctag v l a x hi hp hc (lengthCall ltag tail) line tail index fuel
  have hcount := StationaryProof.iterationCount (T := T) (G := [E]) itag _ _ (state ptag .zero code) index fuel (.base hlen)
  have he := localTrans _ _ _ hcount (.base hs)
  have hE : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hmap : Derivation T (.imp E F) := Hilbert.Local.finish (Hilbert.Local.discharge
    (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) hE))
  have hP : Hilbert.Local T ctx [P] P := .hypothesis List.mem_cons_self
  have hn : Hilbert.Local T ctx [P] (.neg F) := .mp (.base (noneElim itag ltag ptag tail out index fuel)) hP
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base (contraposition E F)) (.base hmap)) hn))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StepSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.StepSupportProof
