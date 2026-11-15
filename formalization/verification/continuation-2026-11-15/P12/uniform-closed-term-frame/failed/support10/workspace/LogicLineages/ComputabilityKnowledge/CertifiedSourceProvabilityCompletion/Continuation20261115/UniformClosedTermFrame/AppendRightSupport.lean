module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryAppend
open HistoryAppend.PreserveSupportProof (substAppend)
def property {ctx : Nat} (tag : Nat) (left : Term ctx) : Formula ctx :=
 .equal (appendCall tag left .zero) left
theorem substProperty {m n : Nat} (s : Fin m → Term n) tag (left : Term m) :
 substituteFormula s (property tag left) = property tag (substitute s left) := by
 simp only [property,substituteFormula,substAppend,substitute]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} tag (a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property tag a) (property tag b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property tag (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,Fin.cases_zero] using h

theorem nilRight {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,append⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property (ctx := ctx) tag .zero)) :=
 AppendEquationsProof.internalAppendNil n p tag ht ctx .zero
/-- Original positive append recurrence and actual decoder reconstruction. -/
theorem positive {n ctx : Nat} (p : Program n) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,append⟩) (count : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (property tag (call (PositiveProof.inputTailTag tag) (.succ count ::ᵥ nil)))
   (property tag (.succ count)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let tail := call (PositiveProof.inputTailTag tag) (.succ count ::ᵥ nil)
 let head := call (PositiveProof.inputHeadTag tag) (.succ count ::ᵥ nil)
 let ct := PositiveProof.outputConsTag tag
 let H := property tag tail
 have ih : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hv := TableEquationsProof.valueInstalled p (AppendEquationsProof.tableTag tag)
  (AppendEquationsProof.tableInstalled p tag ht)
 obtain ⟨hc,hhead,htail,_,_,_⟩ := ValueEquationsProof.valueNodes p (PositiveProof.valueAt tag) hv
 obtain ⟨ha⟩ := PositiveProof.appendPositive p tag ht count (.zero : Term ctx)
 obtain ⟨hr⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ct
  (PositiveProof.inputHeadTag tag) (PositiveProof.inputTailTag tag) hc hhead htail ctx count
 have hcons := HistoryIteratorSuffix.StepSuffixProof.pairCongruence (T := T) (G := [H]) ct
  head (appendCall tag tail .zero) head tail (.base (.logical (.reflexive head))) ih
 exact ⟨(localTrans _ _ _ (.base ha) (localTrans _ _ _ hcons (.base hr))).discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightSupport
