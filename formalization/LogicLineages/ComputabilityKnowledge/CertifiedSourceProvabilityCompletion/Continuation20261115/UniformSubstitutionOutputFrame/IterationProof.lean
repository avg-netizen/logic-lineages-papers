module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.AllStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport TransformProof
open UniformClosedSubstitutionFold (iterateCall)
open LiteralRawMP.DispatcherSupportProof
def property {ctx : Nat} (ptag ftag ltag rtag itag : Nat) (count prefixCode state raw : Term ctx) : Formula ctx :=
 .equal (iterateCall itag count (transformed ptag ftag ltag rtag prefixCode state) raw)
  (transformed ptag ftag ltag rtag prefixCode (iterateCall itag count state raw))
theorem substProperty {m n : Nat} (s : Fin m → Term n) ptag ftag ltag rtag itag (count prefixCode state raw : Term m) :
 substituteFormula s (property ptag ftag ltag rtag itag count prefixCode state raw) =
 property ptag ftag ltag rtag itag (substitute s count) (substitute s prefixCode) (substitute s state) (substitute s raw) := by
 simp only [property,iterateCall,substituteFormula,substTransformed,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem base {n ctx : Nat} (p : Program n) (ptag ftag ltag rtag itag : Nat)
 (hi : (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩) (prefixCode state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ptag ftag ltag rtag itag .zero prefixCode state raw)) := by
 obtain ⟨hleft⟩ := UniformClosedSubstitutionFold.IterationProof.zero p itag hi (transformed ptag ftag ltag rtag prefixCode state) raw
 obtain ⟨hright⟩ := UniformClosedSubstitutionFold.IterationProof.zero p itag hi state raw
 have hmap := TickCasesProof.transformCongruence ptag ftag ltag rtag prefixCode _ _ hright
 exact ⟨Logic.trans _ _ _ hleft (Support.equalitySymmetry _ _ hmap)⟩
theorem step {n ctx : Nat} (p : Program n) (ptag ftag atag ltag rtag itag ctag stag etag htag tailtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,outputFrame⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hi : (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (htail : (nodes p)[tailtag]? = some ⟨1,HistoryLookup.tail⟩) (count prefixCode state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (property ptag ftag ltag rtag itag count prefixCode state raw)
   (property ptag ftag ltag rtag itag (.succ count) prefixCode state raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := property ptag ftag ltag rtag itag count prefixCode state raw
 have hih : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 let ttag := UniformClosedSubstitutionFold.IterationProof.tickTag itag
 have ht := UniformClosedSubstitutionFold.IterationProof.tickInstalled p itag hi
 obtain ⟨hleft⟩ := UniformClosedSubstitutionFold.IterationProof.successor p itag hi count (transformed ptag ftag ltag rtag prefixCode state) raw
 obtain ⟨hright⟩ := UniformClosedSubstitutionFold.IterationProof.successor p itag hi count state raw
 obtain ⟨htick⟩ := AllStateProof.arbitraryState p ptag ftag atag ltag rtag ttag ctag stag etag htag tailtag
  hp hf ha hl hr ht hc hs he hh htail prefixCode (iterateCall itag count state raw) raw
 have hm := callCongruence (T := T) (G := [H]) ttag
  (iterateCall itag count (transformed ptag ftag ltag rtag prefixCode state) raw ::ᵥ raw ::ᵥ nil)
  (transformed ptag ftag ltag rtag prefixCode (iterateCall itag count state raw) ::ᵥ raw ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact hih
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive raw))
     | succ i => exact Fin.elim0 i)
 have hend := TickCasesProof.transformCongruence ptag ftag ltag rtag prefixCode _ _ hright
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base hleft) (localTrans _ _ _ hm
   (localTrans _ _ _ (.base htick) (.base (Support.equalitySymmetry _ _ hend))))))⟩
theorem arbitraryCount {n ctx : Nat} (p : Program n) (ptag ftag atag ltag rtag itag ctag stag etag htag tailtag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hf : (nodes p)[ftag]? = some ⟨2,outputFrame⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (hi : (nodes p)[itag]? = some ⟨3,UniformClosedSubstitutionFold.iterator⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩)
 (htail : (nodes p)[tailtag]? = some ⟨1,HistoryLookup.tail⟩) (count prefixCode state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property ptag ftag ltag rtag itag count prefixCode state raw)) := by
 let phi : Formula (ctx+1) := property ptag ftag ltag rtag itag (.var 0) (liftTerm prefixCode) (liftTerm state) (liftTerm raw)
 obtain ⟨hz⟩ := base p ptag ftag ltag rtag itag hi prefixCode state raw
 have hb : Derivation (GorbowPRNumeralCalculation.Theory p) (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
 obtain ⟨hs0⟩ := step p ptag ftag atag ltag rtag itag ctag stag etag htag tailtag hp hf ha hl hr hi hc hs he hh htail
  (.var 0 : Term (ctx+1)) (liftTerm prefixCode) (liftTerm state) (liftTerm raw)
 have hs1 : Derivation (GorbowPRNumeralCalculation.Theory p) (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substProperty,substitute,successorLift,Fin.cases_zero,Support.shiftCancel] using hs0
 have h := atTerm phi count (induction phi hb hs1)
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.IterationProof
