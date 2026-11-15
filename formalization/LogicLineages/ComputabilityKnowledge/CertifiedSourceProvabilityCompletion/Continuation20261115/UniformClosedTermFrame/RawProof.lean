module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStepProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport InvariantProof BoundProof
noncomputable def generalizeStates {T : Sentence → Prop} {ctx : Nat} ftag stag ptag ctag atag len q l r
 (H : Formula ctx) (tokens raw : Term ctx)
 (h : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken H))))
  (property ftag stag ptag ctag atag len q l r (liftTerm (liftTerm (liftTerm (liftTerm tokens)))) (liftTerm (liftTerm (liftTerm (liftTerm raw)))) (.var 3) (.var 2) (.var 1) (.var 0)))) :
 Derivation T (.imp H (allStates ftag stag ptag ctag atag len q l r tokens raw)) := by
 have hf2 : Fin.succ (2 : Fin (ctx+3)) = (3 : Fin (ctx+4)) := rfl
 have h1 := HistoryIteratorSuffix.RelationProof.universalUnder _ _ h
 have h1' : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken H)))
  (allOutputs ftag stag ptag ctag atag len q l r (liftTerm (liftTerm (liftTerm tokens))) (liftTerm (liftTerm (liftTerm raw)))
   (.var (2 : Fin (ctx+3))) (.var 1) (.var 0))) := by
  simpa only [allOutputs,liftTerm,renameTerm,substitute,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,hf2] using h1
 have h2 := HistoryIteratorSuffix.RelationProof.universalUnder _ _ h1'
 have h2' : Derivation T (.imp (GorbowPACore.weaken (GorbowPACore.weaken H))
  (allRests ftag stag ptag ctag atag len q l r (liftTerm (liftTerm tokens)) (liftTerm (liftTerm raw))
   (.var (1 : Fin (ctx+2))) (.var 0))) := by
  simpa only [allRests,liftTerm,renameTerm,substitute,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] using h2
 have h3 := HistoryIteratorSuffix.RelationProof.universalUnder _ _ h2'
 have h3' : Derivation T (.imp (GorbowPACore.weaken H)
  (allPrefixes ftag stag ptag ctag atag len q l r (liftTerm tokens) (liftTerm raw) (.var (0 : Fin (ctx+1))))) := by
  simpa only [allPrefixes,liftTerm,renameTerm,substitute,Fin.succ_zero_eq_one] using h3
 exact HistoryIteratorSuffix.RelationProof.universalUnder _ _ h3'
theorem nilAll {n ctx : Nat} (p : Program n) (ftag stag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩) (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allStates ftag stag ptag ctag atag len q l r .zero raw)) := by
 obtain ⟨h⟩ := NilProof.nil (ctx := ctx+4) p ftag stag ptag ctag atag len q l r hf hs hp hc ha hlen
  (liftTerm (liftTerm (liftTerm (liftTerm raw)))) (.var 3) (.var 2) (.var 1) (.var 0)
 exact ⟨.generalize (.generalize (.generalize (.generalize h)))⟩
theorem consAll {n ctx : Nat} (p : Program n)
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)

 (token tokens raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (allStates ftag stag ptag ctag atag len q l r tokens raw)
   (allStates ftag stag ptag ctag atag len q l r (HistoryLookup.consCall ctag token tokens) raw))) := by
 let H := allStates ftag stag ptag ctag atag len q l r tokens raw
 obtain ⟨h⟩ := OldStepProof.cons (ctx := ctx+4) p ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd (liftTerm (liftTerm (liftTerm (liftTerm token)))) (liftTerm (liftTerm (liftTerm (liftTerm tokens)))) (liftTerm (liftTerm (liftTerm (liftTerm raw))))
  (.var 3) (.var 2) (.var 1) (.var 0)
 have h' : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken H))))
   (property ftag stag ptag ctag atag len q l r (liftTerm (liftTerm (liftTerm (liftTerm (HistoryLookup.consCall ctag token tokens))))) (liftTerm (liftTerm (liftTerm (liftTerm raw))))
    (.var 3) (.var 2) (.var 1) (.var 0))) := by
  simpa only [H,OldStackProof.claim,GorbowPACore.weaken,substAllStates,liftTerm,renameTerm,
   HistoryLookup.DropEquationsProof.substCons] using h
 exact ⟨generalizeStates ftag stag ptag ctag atag len q l r H (HistoryLookup.consCall ctag token tokens) raw h'⟩
/-- Every positive numeric raw code is recovered as actual head/encoded tail;
original decoder bound gives tail≤predecessor for the internal bounded IH. -/
theorem positive {n ctx : Nat} (p : Program n)
 (ftag stag stepTag etag xtag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hst : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (dtag : Nat) (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)

 (count raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (bounded ftag stag ptag ctag atag len q l r count raw) (allStates ftag stag ptag ctag atag len q l r (.succ count) raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := bounded ftag stag ptag ctag atag len q l r count raw
 let vt := HistoryAppend.PositiveProof.valueAt atag
 let ht := HistoryAppend.PositiveProof.inputHeadTag atag
 let tt := HistoryAppend.PositiveProof.inputTailTag atag
 let head := call ht (.succ count ::ᵥ nil)
 let tail := call tt (.succ count ::ᵥ nil)
 have hval := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨_,hhead,htail,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p vt hval
 obtain ⟨hb⟩ := HistoryDecoderBounds.OuterRangeProof.internalPositiveTailBound n p tt htail ctx count
 obtain ⟨heq⟩ := HistoryIteratorSuffix.ReconstructionProof.internalListReconstruction n p ctag ht tt hc hhead htail ctx count
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hih := Hilbert.Local.mp (.mp (.base (boundedInstance ftag stag ptag ctag atag len q l r count tail raw)) hh) (.base hb)
 obtain ⟨hcns⟩ := consAll p ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd head tail raw
 have hrow := Hilbert.Local.mp (.base hcns) hih
 have hout := Hilbert.Local.mp (.mp (.base (transportAll ftag stag ptag ctag atag len q l r
  (HistoryLookup.consCall ctag head tail) (.succ count) raw)) (.base heq)) hrow
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.RawProof
