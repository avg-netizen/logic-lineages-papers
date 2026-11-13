module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneSupportProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Fusion FusionAlgebraProof HistoryBounds

def property {ctx : Nat} (itag ltag ptag rtag : Nat) (raw : Term ctx) : Formula ctx :=
 .equal (scanState itag ltag ptag rtag raw .zero) .zero
def bounded {ctx : Nat} (itag ltag ptag rtag : Nat) (bound : Term ctx) : Formula ctx :=
 .all (.imp (weakBound (.var 0) (liftTerm bound)) (property itag ltag ptag rtag (.var 0)))
theorem substProperty {m n : Nat} (sub : Fin m → Term n) itag ltag ptag rtag (raw : Term m) :
 substituteFormula sub (property itag ltag ptag rtag raw) = property itag ltag ptag rtag (substitute sub raw) := by
 simp only [property,substituteFormula,substScanState,substitute]
theorem substBounded {m n : Nat} (sub : Fin m → Term n) itag ltag ptag rtag (bound : Term m) :
 substituteFormula sub (bounded itag ltag ptag rtag bound) = bounded itag ltag ptag rtag (substitute sub bound) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substProperty,
  HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} itag ltag ptag rtag (bound code : Term ctx) :
 Derivation T (.imp (bounded itag ltag ptag rtag bound)
  (.imp (weakBound code bound) (property itag ltag ptag rtag code))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (weakBound (.var 0) (liftTerm bound)) (property itag ltag ptag rtag (.var 0))) code)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,bounded] using h
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} itag ltag ptag rtag (a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property itag ltag ptag rtag a) (property itag ltag ptag rtag b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property itag ltag ptag rtag (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,substitute,Fin.cases_zero] using h

section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag ctag stag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
variable (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
variable (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
include hi hl hp hr

theorem base : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (bounded (ctx := ctx) itag ltag ptag rtag .zero)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := StateRecursionProof.nil p itag ltag ptag rtag hi hl hp hr (.zero : Term (ctx+1))
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (.mp (.base (transport itag ltag ptag rtag .zero code)) hcode) (.base hz)
 exact ⟨.generalize (Hilbert.Local.finish (Hilbert.Local.discharge hout))⟩

omit hr in
include ha hc hs in
theorem positive (count : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded itag ltag ptag rtag count) (property itag ltag ptag rtag (.succ count)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := bounded itag ltag ptag rtag count
 let vt := HistoryAppend.PositiveProof.valueAt atag
 let ht := HistoryAppend.PositiveProof.inputHeadTag atag
 let tt := HistoryAppend.PositiveProof.inputTailTag atag
 let head := call ht (.succ count ::ᵥ nil)
 let tail := call tt (.succ count ::ᵥ nil)
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨_,hhead,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p vt hv
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p tt htail ctx count
 obtain ⟨he⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag ht tt hc hhead htail ctx count
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have ih := Hilbert.Local.mp (.mp (.base (instanceRule itag ltag ptag rtag count tail)) hh) (.base hb)
 obtain ⟨hcns⟩ := StateRecursionProof.cons p itag ltag ptag rtag ctag stag hi hl hp hc hs head tail (.zero : Term ctx)
 obtain ⟨hnone⟩ := LiteralSyntaxStep.StepProof.internalNone n p stag hs ctx head
 have hnext := scanCongruence (T := T) (G := [H]) itag ltag ptag rtag tail tail _ .zero
  (.base (.logical (.reflexive tail))) (.base hnone)
 have hrow := localTrans _ _ _ (.base hcns) (localTrans _ _ _ hnext ih)
 have hout := Hilbert.Local.mp (.mp (.base (transport itag ltag ptag rtag (HistoryLookup.consCall ctag head tail) (.succ count))) (.base he)) hrow
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.NoneSupportProof
