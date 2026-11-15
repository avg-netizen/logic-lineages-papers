module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightBounded
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds AppendRightSupport

def bounded {ctx : Nat} (tag : Nat) (bound code : Term ctx) : Formula ctx :=
 .imp (weakBound code bound) (property tag code)
def allBounded {ctx : Nat} (tag : Nat) (bound : Term ctx) : Formula ctx :=
 .all (bounded tag (liftTerm bound) (.var 0))
theorem substBounded {m n : Nat} (s : Fin m → Term n) tag (bound code : Term m) :
 substituteFormula s (bounded tag bound code) = bounded tag (substitute s bound) (substitute s code) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substProperty]
theorem substAll {m n : Nat} (s : Fin m → Term n) tag (bound : Term m) :
 substituteFormula s (allBounded tag bound) = allBounded tag (substitute s bound) := by
 simp only [allBounded,substituteFormula,substBounded,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem allAt {ctx : Nat} tag (bound code : Term ctx) :
 GorbowStandardInstances.instantiate (bounded tag (liftTerm bound) (.var 0)) code = bounded tag bound code := by
 simp only [GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
def allElim {T : Sentence → Prop} {ctx : Nat} tag (bound code : Term ctx) :
 Derivation T (.imp (allBounded tag bound) (bounded tag bound code)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (bounded tag (liftTerm bound) (.var 0)) code)
 rwa [GorbowPACore.logicalFormula,allAt] at h

theorem zeroAt {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (bounded tag .zero code)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := weakBound code .zero
 have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hn⟩ := AppendRightSupport.nilRight (ctx := ctx) p tag ht
 have he := HistoryOrder.StepProof.localSym _ _ (Hilbert.Local.mp (.base hz) h)
 have result := Hilbert.Local.mp (.mp (.base (transport tag .zero code)) he) (.base hn)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge result)⟩

theorem newAt {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (bound : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allBounded tag bound) (property tag (.succ bound)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := allBounded tag bound
 let tail := call (HistoryAppend.PositiveProof.inputTailTag tag) (.succ bound ::ᵥ nil)
 have ih : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag tag) (HistoryAppend.AppendEquationsProof.tableInstalled p tag ht)
 obtain ⟨_,_,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p (HistoryAppend.PositiveProof.valueAt tag) hv
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p (HistoryAppend.PositiveProof.inputTailTag tag) htail ctx bound
 have hi := Hilbert.Local.mp (.mp (.base (allElim tag bound tail)) ih) (.base hb)
 obtain ⟨hs⟩ := AppendRightSupport.positive p tag ht bound
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hs) hi))⟩

theorem nextAt {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (bound code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allBounded tag bound) (bounded tag (.succ bound) code))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := allBounded tag bound
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := property tag code
 obtain ⟨hn⟩ := newAt p tag ht bound
 have hp : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hnew := Hilbert.Local.mp (.base hn) hp
 have hleft := Hilbert.Local.mp (.mp (.base (transport tag (.succ bound) code)) he) hnew
 have hl : Derivation T (.imp P (.imp E Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hleft))
 have hp' : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (allElim tag bound code)) hp') hb
 have hr : Derivation T (.imp P (.imp B Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hright))
 let W := weakBound code (.succ bound)
 have hp0 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := LiteralSyntaxFrame.BoundedSupport.weakNext T code bound
 have out := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q))) (.mp (.base hl) hp0)) (.mp (.base hr) hp0)) (.mp (.base hs) hw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge out))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightBounded
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightBounded
