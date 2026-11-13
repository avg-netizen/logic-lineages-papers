module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TrichotomyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryAppend
open HistoryAppend.PreserveSupportProof (substAppend)

def property {ctx : Nat} (tag : Nat) (left middle right : Term ctx) : Formula ctx :=
 .equal (appendCall tag (appendCall tag left middle) right) (appendCall tag left (appendCall tag middle right))
theorem substProperty {m n : Nat} (s : Fin m → Term n) tag (left middle right : Term m) :
 substituteFormula s (property tag left middle right) = property tag (substitute s left) (substitute s middle) (substitute s right) := by
 simp only [property,substituteFormula,substAppend]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} tag (a b middle right : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property tag a middle right) (property tag b middle right))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property tag (.var 0) (liftTerm middle) (liftTerm right)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

noncomputable def binary {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} tag (a b c d : Term ctx)
 (h : Hilbert.Local T ctx G (.equal a c)) (k : Hilbert.Local T ctx G (.equal b d)) :
 Hilbert.Local T ctx G (.equal (appendCall tag a b) (appendCall tag c d)) :=
 HistoryIteratorSuffix.StepSuffixProof.pairCongruence tag a b c d h k

theorem nilAssoc {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,append⟩) (middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property tag .zero middle right)) := by
 obtain ⟨hm⟩ := AppendEquationsProof.internalAppendNil n p tag ht ctx middle
 obtain ⟨hr⟩ := AppendEquationsProof.internalAppendNil n p tag ht ctx (appendCall tag middle right)
 exact ⟨Logic.trans _ _ _ (PositiveProof.binaryCongruence tag _ middle right right hm (.logical (.reflexive right))) (Support.equalitySymmetry _ _ hr)⟩

theorem consAssoc {n ctx : Nat} (p : Program n) (tag ctag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,append⟩) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (head tail middle right : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (property tag tail middle right) (property tag (HistoryLookup.consCall ctag head tail) middle right))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := property tag tail middle right
 have ih : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hm⟩ := ConsProof.internalAppendCons n p tag ctag ht hc ctx head tail middle
 obtain ⟨hr⟩ := ConsProof.internalAppendCons n p tag ctag ht hc ctx head (appendCall tag tail middle) right
 obtain ⟨hb⟩ := ConsProof.internalAppendCons n p tag ctag ht hc ctx head tail (appendCall tag middle right)
 have h1 := binary tag _ right _ right (Hilbert.Local.base (Gamma := [H]) hm) (.base (.logical (.reflexive right)))
 have h2 := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ctag head _ head _ (.base (.logical (.reflexive head))) ih
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ h1 (localTrans _ _ _ (.base hr) (localTrans _ _ _ h2 (HistoryOrder.StepProof.localSym _ _ (.base hb))))))⟩
/-- The actual append recurrence itself supplies the cons image; no input
reconstruction hypothesis is needed. -/
theorem positive {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,append⟩) (count middle right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (property tag (call (PositiveProof.inputTailTag tag) (.succ count ::ᵥ nil)) middle right)
    (property tag (.succ count) middle right))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let tail := call (PositiveProof.inputTailTag tag) (.succ count ::ᵥ nil)
 let head := call (PositiveProof.inputHeadTag tag) (.succ count ::ᵥ nil)
 let ct := PositiveProof.outputConsTag tag
 let H := property tag tail middle right
 have ih : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hv := TableEquationsProof.valueInstalled p (AppendEquationsProof.tableTag tag) (AppendEquationsProof.tableInstalled p tag ht)
 obtain ⟨hc,_,_,_,_,_⟩ := ValueEquationsProof.valueNodes p (PositiveProof.valueAt tag) hv
 obtain ⟨hm⟩ := PositiveProof.appendPositive p tag ht count middle
 obtain ⟨hr⟩ := ConsProof.internalAppendCons n p tag ct ht hc ctx head (appendCall tag tail middle) right
 obtain ⟨hb⟩ := PositiveProof.appendPositive p tag ht count (appendCall tag middle right)
 have h1 := binary tag _ right _ right (Hilbert.Local.base (Gamma := [H]) hm) (.base (.logical (.reflexive right)))
 have h2 := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ct head _ head _ (.base (.logical (.reflexive head))) ih
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ h1 (localTrans _ _ _ (.base hr) (localTrans _ _ _ h2 (HistoryOrder.StepProof.localSym _ _ (.base hb))))))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendSupport
