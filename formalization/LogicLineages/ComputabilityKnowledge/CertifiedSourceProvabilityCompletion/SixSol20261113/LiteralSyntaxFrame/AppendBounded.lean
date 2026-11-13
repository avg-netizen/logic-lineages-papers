module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.BoundedSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendBounded
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds AppendSupport

def bounded {ctx : Nat} (tag : Nat) (bound code middle right : Term ctx) : Formula ctx :=
 .imp (weakBound code bound) (property tag code middle right)
def allBounded {ctx : Nat} (tag : Nat) (bound middle right : Term ctx) : Formula ctx :=
 .all (bounded tag (liftTerm bound) (.var 0) (liftTerm middle) (liftTerm right))
theorem substBounded {m n : Nat} (s : Fin m → Term n) tag (bound code middle right : Term m) :
 substituteFormula s (bounded tag bound code middle right) = bounded tag (substitute s bound) (substitute s code) (substitute s middle) (substitute s right) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substProperty]
theorem substAll {m n : Nat} (s : Fin m → Term n) tag (bound middle right : Term m) :
 substituteFormula s (allBounded tag bound middle right) = allBounded tag (substitute s bound) (substitute s middle) (substitute s right) := by
 simp only [allBounded,substituteFormula,substBounded,HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
theorem allAt {ctx : Nat} tag (bound code middle right : Term ctx) :
 GorbowStandardInstances.instantiate (bounded tag (liftTerm bound) (.var 0) (liftTerm middle) (liftTerm right)) code = bounded tag bound code middle right := by
 simp only [GorbowStandardInstances.instantiate,substBounded,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
def allElim {T : Sentence → Prop} {ctx : Nat} tag (bound code middle right : Term ctx) :
 Derivation T (.imp (allBounded tag bound middle right) (bounded tag bound code middle right)) := by
 have h := Derivation.logical (A := T) (.allInstantiate (bounded tag (liftTerm bound) (.var 0) (liftTerm middle) (liftTerm right)) code)
 rwa [GorbowPACore.logicalFormula,allAt] at h

theorem zeroAt {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (code middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (bounded tag .zero code middle right)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := weakBound code .zero
 have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hn⟩ := AppendSupport.nilAssoc p tag ht middle right
 have he := HistoryOrder.StepProof.localSym _ _ (Hilbert.Local.mp (.base hz) h)
 have result := Hilbert.Local.mp (.mp (.base (transport tag .zero code middle right)) he) (.base hn)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge result)⟩

theorem newAt {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (bound middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allBounded tag bound middle right) (property tag (.succ bound) middle right))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := allBounded tag bound middle right
 let tail := call (HistoryAppend.PositiveProof.inputTailTag tag) (.succ bound ::ᵥ nil)
 have ih : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag tag) (HistoryAppend.AppendEquationsProof.tableInstalled p tag ht)
 obtain ⟨_,_,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p (HistoryAppend.PositiveProof.valueAt tag) hv
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p (HistoryAppend.PositiveProof.inputTailTag tag) htail ctx bound
 have hi := Hilbert.Local.mp (.mp (.base (allElim tag bound tail middle right)) ih) (.base hb)
 obtain ⟨hs⟩ := AppendSupport.positive p tag ht bound middle right
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hs) hi))⟩

theorem nextAt {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,HistoryAppend.append⟩) (bound code middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allBounded tag bound middle right) (bounded tag (.succ bound) code middle right))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let P := allBounded tag bound middle right
 let E := Formula.equal (.succ bound) code
 let B := weakBound code bound
 let Q := property tag code middle right
 obtain ⟨hn⟩ := newAt p tag ht bound middle right
 have hp : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
 have hnew := Hilbert.Local.mp (.base hn) hp
 have hleft := Hilbert.Local.mp (.mp (.base (transport tag (.succ bound) code middle right)) he) hnew
 have hl : Derivation T (.imp P (.imp E Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hleft))
 have hp' : Hilbert.Local T ctx [B,P] P := .hypothesis (by simp)
 have hb : Hilbert.Local T ctx [B,P] B := .hypothesis List.mem_cons_self
 have hright := Hilbert.Local.mp (.mp (.base (allElim tag bound code middle right)) hp') hb
 have hr : Derivation T (.imp P (.imp B Q)) := Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hright))
 let W := weakBound code (.succ bound)
 have hp0 : Hilbert.Local T ctx [W,P] P := .hypothesis (by simp)
 have hw : Hilbert.Local T ctx [W,P] W := .hypothesis List.mem_cons_self
 obtain ⟨hs⟩ := BoundedSupport.weakNext T code bound
 have out := Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim E B Q))) (.mp (.base hl) hp0)) (.mp (.base hr) hp0)) (.mp (.base hs) hw)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge out))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendBounded
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendBounded
