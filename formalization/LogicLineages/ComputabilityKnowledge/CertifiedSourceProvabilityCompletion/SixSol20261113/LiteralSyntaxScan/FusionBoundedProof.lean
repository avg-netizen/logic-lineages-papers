module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionAlgebraProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.BoundedSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionBoundedProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Fusion FusionAlgebraProof HistoryBounds

theorem substBounded {m n : Nat} (sub : Fin m → Term n) itag ltag ptag rtag atag (bound right : Term m) :
 substituteFormula sub (boundedFusion itag ltag ptag rtag atag bound right) =
 boundedFusion itag ltag ptag rtag atag (substitute sub bound) (substitute sub right) := by
 simp only [boundedFusion,substituteFormula,HistoryBounds.SupportProof.substWeak,substAllFusion,
  HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]

noncomputable def boundedInstance {T : Sentence → Prop} {ctx : Nat}
 (itag ltag ptag rtag atag : Nat) (bound code right : Term ctx) :
 Derivation T (.imp (boundedFusion itag ltag ptag rtag atag bound right)
  (.imp (weakBound code bound) (allFusion itag ltag ptag rtag atag code right))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (weakBound (.var 0) (liftTerm bound))
   (allFusion itag ltag ptag rtag atag (.var 0) (liftTerm right))) code)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substAllFusion,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,boundedFusion] using h

noncomputable def transportAll {T : Sentence → Prop} {ctx : Nat}
 (itag ltag ptag rtag atag : Nat) (a b right : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (allFusion itag ltag ptag rtag atag a right)
  (allFusion itag ltag ptag rtag atag b right))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (allFusion itag ltag ptag rtag atag (.var 0) (liftTerm right)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAllFusion,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

noncomputable def transportFusion {T : Sentence → Prop} {ctx : Nat}
 (itag ltag ptag rtag atag : Nat) (a b right state : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (fusion itag ltag ptag rtag atag a right state)
  (fusion itag ltag ptag rtag atag b right state))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (fusion itag ltag ptag rtag atag (.var 0) (liftTerm right) (liftTerm state)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substFusion,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

section
variable {n ctx : Nat} (p : Program n) (itag ltag ptag rtag atag : Nat)
variable (hi : (nodes p)[itag]? = some ⟨2,iterator⟩)
variable (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
variable (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
variable (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
variable (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)

theorem nilAll (right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (allFusion itag ltag ptag rtag atag .zero right)) := by
 obtain ⟨h⟩ := nilFusion p itag ltag ptag rtag atag hi hl hp hr ha
  (liftTerm right) (.var (0 : Fin (ctx+1)))
 exact ⟨.generalize h⟩

theorem base (right : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (boundedFusion itag ltag ptag rtag atag .zero right)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let code : Term (ctx+1) := .var 0
 let H := weakBound code .zero
 have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryIteratorDrain.BoundSupportProof.weakZero T code
 obtain ⟨hz⟩ := nilAll p itag ltag ptag rtag atag hi hl hp hr ha (liftTerm right)
 have hcode := HistoryOrder.StepProof.localSym _ _ (.mp (.base he) hh)
 have hout := Hilbert.Local.mp (Hilbert.Local.mp
  (.base (transportAll itag ltag ptag rtag atag .zero code (liftTerm right))) hcode) (.base hz)
 exact ⟨.generalize (Hilbert.Local.finish (Hilbert.Local.discharge hout))⟩

theorem positiveAt (ctag stag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (count right state : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (boundedFusion itag ltag ptag rtag atag count right)
   (fusion itag ltag ptag rtag atag (.succ count) right state))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := boundedFusion itag ltag ptag rtag atag count right
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
 have ih : Hilbert.Local T ctx [H] (allFusion itag ltag ptag rtag atag tail right) :=
  .mp (.mp (.base (boundedInstance itag ltag ptag rtag atag count tail right)) hh) (.base hb)
 obtain ⟨hcns⟩ := consFusion p itag ltag ptag rtag atag hi hl hp ha ctag stag hc hs head tail right state
 have hout := Hilbert.Local.mp (Hilbert.Local.mp
  (.base (transportFusion itag ltag ptag rtag atag (HistoryLookup.consCall ctag head tail)
    (.succ count) right state)) (.base he)) (.mp (.base hcns) ih)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionBoundedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionBoundedProof
