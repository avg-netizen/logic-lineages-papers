module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset
open PrefixSupportProof

/-- Pure internal composition: the two supplied equalities are actual one-step
kernel equations, not additional object-theory premises. -/
theorem consCase {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (line tail right option next out index fuel : Term ctx)
    (hs : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (run itag ptag (.succ (lengthCall ltag tail)) option (HistoryLookup.consCall ctag line tail) index fuel)
        (run itag ptag (lengthCall ltag tail) next tail index fuel)))
    (ht : Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (run itag ptag (.succ (lengthCall ltag tail)) option
          (HistoryLookup.consCall ctag line (HistoryAppend.appendCall atag tail right)) index fuel)
        (run itag ptag (lengthCall ltag tail) next (HistoryAppend.appendCall atag tail right) index fuel))) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag atag ptag tail right index fuel)
        (relation itag ltag atag ptag (HistoryLookup.consCall ctag line tail) right option out index fuel))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := HistoryLookup.consCall ctag line tail
  let P := property itag ltag atag ptag tail right index fuel
  let H := Formula.equal (run itag ptag (lengthCall ltag code) option code index fuel) (state ptag out .zero)
  have ih : Hilbert.Local T ctx [H,P] P := .hypothesis (by simp)
  have h : Hilbert.Local T ctx [H,P] H := .hypothesis List.mem_cons_self
  obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx line tail
  have hcount := StationaryProof.iterationCount (T := T) (G := [H,P]) itag _ (.succ (lengthCall ltag tail)) (state ptag option code) index fuel (.base hlen)
  have hleft := localTrans _ _ _ hcount (.base hs)
  have hin := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hleft) h
  have hout := Hilbert.Local.mp (.mp (.base (propertyElim itag ltag atag ptag tail right next out index fuel)) ih) hin
  obtain ⟨happ⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx line tail right
  have happState := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag option _ option _
    (Hilbert.Local.base (Gamma := [H,P]) (.logical (.reflexive option))) (.base happ)
  have happRun := StationaryProof.iterationState itag (lengthCall ltag code) _ _ index fuel happState
  have hc2 := StationaryProof.iterationCount (T := T) (G := [H,P]) itag _ (.succ (lengthCall ltag tail))
    (state ptag option (HistoryLookup.consCall ctag line (HistoryAppend.appendCall atag tail right))) index fuel (.base hlen)
  have he := localTrans _ _ _ happRun (localTrans _ _ _ hc2 (localTrans _ _ _ (.base ht) hout))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge he))⟩

theorem someCase {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail right history out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag atag ptag tail right index fuel)
        (relation itag ltag atag ptag (HistoryLookup.consCall ctag line tail) right (.succ history) out index fuel))) := by
  obtain ⟨hs⟩ := ConsRunProof.someCons p itag ptag ctag v l a x hi hp hc (lengthCall ltag tail) history line tail index fuel
  obtain ⟨ht⟩ := ConsRunProof.someCons p itag ptag ctag v l a x hi hp hc (lengthCall ltag tail) history line (HistoryAppend.appendCall atag tail right) index fuel
  exact consCase p itag ltag atag ptag ctag hl ha hc line tail right (.succ history) _ out index fuel hs ht

theorem noneCase {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line tail right out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (property itag ltag atag ptag tail right index fuel)
        (relation itag ltag atag ptag (HistoryLookup.consCall ctag line tail) right .zero out index fuel))) := by
  obtain ⟨hs⟩ := ConsRunProof.noneCons p itag ptag ctag v l a x hi hp hc (lengthCall ltag tail) line tail index fuel
  obtain ⟨ht⟩ := ConsRunProof.noneCons p itag ptag ctag v l a x hi hp hc (lengthCall ltag tail) line (HistoryAppend.appendCall atag tail right) index fuel
  exact consCase p itag ltag atag ptag ctag hl ha hc line tail right .zero .zero out index fuel hs ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixConsProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.PrefixConsProof
