module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.NilProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryLengthOffset HistoryRunSplice SupportProof

theorem nilNone {n ctx : Nat} (p : Program n) (itag ltag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (noneRelation itag ltag ptag .zero out index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (run itag ptag (lengthCall ltag .zero) .zero .zero index fuel) (state ptag (.succ out) .zero)
  have h : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  obtain ⟨hz⟩ := ConsRunProof.nilLength p itag ltag ptag v l a x hi hl (.zero : Term ctx) .zero index fuel
  obtain ⟨hn⟩ := HistoryIteratorSuffix.NoneImageProof.noneNotSome p ptag hp (.zero : Term ctx) out .zero
  have himp := Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hz)) h))
  exact ⟨Hilbert.modusTollens himp hn⟩

theorem nilSome {n ctx : Nat} (p : Program n) (itag ltag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (history out index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (someRelation itag ltag ptag .zero history out index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (run itag ptag (lengthCall ltag .zero) (.succ history) .zero index fuel) (state ptag (.succ out) .zero)
  have h : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  obtain ⟨hz⟩ := ConsRunProof.nilLength p itag ltag ptag v l a x hi hl (.succ history) (.zero : Term ctx) index fuel
  have he := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hz)) h
  obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p ptag hp ctx (.succ history) .zero (.succ out) .zero
  have hs : Hilbert.Local T ctx [E] (.equal (.succ history) (.succ out)) := .mp (.base (.logical (.andLeft _ _))) (.mp (.base hinj) he)
  have hho : Hilbert.Local T ctx [E] (.equal history out) := .mp (.base (.arithmetic (.succInjective _ _))) hs
  have hlen := LengthDataSupportProof.lengthCongruence ltag out history (HistoryOrder.StepProof.localSym _ _ hho)
  obtain ⟨hlen0⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
  have hadd := localUnary (.add (liftTerm (lengthCall ltag history)) (.var 0)) _ _ (Hilbert.Local.base (Gamma := [E]) hlen0)
  simp only [GorbowSubstitution.substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] at hadd
  have hsum := localTrans _ _ _ hadd (.base (.arithmetic (.addZero (lengthCall ltag history))))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hlen (HistoryOrder.StepProof.localSym _ _ hsum)))⟩

theorem nilProperty {n ctx : Nat} (p : Program n) (itag ltag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property itag ltag ptag .zero index fuel)) := by
  obtain ⟨hn⟩ := nilNone p itag ltag ptag v l a x hi hl hp (.var (0 : Fin (ctx+1))) (liftTerm index) (liftTerm fuel)
  obtain ⟨hs⟩ := nilSome p itag ltag ptag v l a x hi hl hp (.var (1 : Fin (ctx+2))) (.var 0) (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
  have hn' : Derivation (GorbowPRNumeralCalculation.Theory p) (noneAll itag ltag ptag .zero index fuel) := .generalize hn
  have hs' : Derivation (GorbowPRNumeralCalculation.Theory p) (someAll itag ltag ptag .zero index fuel) := .generalize (.generalize hs)
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hn') hs'⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.NilProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthConservation.NilProof
