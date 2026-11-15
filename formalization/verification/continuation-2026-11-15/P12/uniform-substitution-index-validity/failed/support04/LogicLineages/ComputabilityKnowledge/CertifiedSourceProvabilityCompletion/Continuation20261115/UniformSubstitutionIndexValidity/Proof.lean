module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LogicProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem lower {n ctx : Nat} (p : Program n) (etag vtag stag ptag ctag atag dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (index depth positive rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (HistoryBounds.strictBound index depth) (claim etag vtag stag ptag ctag dtag index depth positive rest raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.lowerBody index depth
 let V := RawReflexivityDispatcher.valid vtag (liftTerm raw)
 let P := Formula.equal (HistoryDifference.differenceCall dtag (liftTerm index) (.succ (liftTerm depth))) (.succ (liftTerm positive))
 let G := [P,V,H]
 have hh : Hilbert.Local T (ctx+1) G (.equal (liftTerm depth) (.add (liftTerm index) (.succ (.var 0)))) :=
  .hypothesis (by simp [G,H,HistoryOrder.lowerBody])
 obtain ⟨hout⟩ := BranchProof.below p G etag stag ptag ctag dtag he hs hp hc hd
  (liftTerm index) (liftTerm depth) (.var 0) (liftTerm rest) (liftTerm raw) (HistoryOrder.StepProof.localSym _ _ hh)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (claim etag vtag stag ptag ctag dtag index depth positive rest raw))) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [G,V,P,claim,outputValid,liftTerm,renameTerm] using hout.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H (claim etag vtag stag ptag ctag dtag index depth positive rest raw) ⟨hb⟩
theorem upper {n ctx : Nat} (p : Program n) (etag vtag stag ptag ctag atag dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (index depth positive rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (HistoryBounds.strictBound depth index) (claim etag vtag stag ptag ctag dtag index depth positive rest raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryOrder.lowerBody depth index
 let V := RawReflexivityDispatcher.valid vtag (liftTerm raw)
 let P := Formula.equal (HistoryDifference.differenceCall dtag (liftTerm index) (.succ (liftTerm depth))) (.succ (liftTerm positive))
 let G := [P,V,H]
 have hh : Hilbert.Local T (ctx+1) G (.equal (liftTerm index) (.add (liftTerm depth) (.succ (.var 0)))) :=
  .hypothesis (by simp [G,H,HistoryOrder.lowerBody])
 have hpositive : Hilbert.Local T (ctx+1) G P := .hypothesis (by simp [G])
 obtain ⟨hz⟩ := AboveProof.differenceZeroAbove p G dtag hd (liftTerm index) (liftTerm depth) (.var 0) hh
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hpositive) hz
 have hout : Hilbert.Local T (ctx+1) G (outputValid etag stag ptag ctag (liftTerm index) (liftTerm depth) (liftTerm rest) (liftTerm raw)) :=
  Hilbert.Local.explosion _ hbad (.base (.arithmetic (.succNotZero (liftTerm positive))))
 have hb : Derivation T (.imp H (GorbowPACore.weaken (claim etag vtag stag ptag ctag dtag index depth positive rest raw))) := by
  rw [GorbowPACore.weaken,substClaim]
  simpa only [G,V,P,claim,liftTerm,renameTerm] using hout.discharge.discharge.discharge.finish
 exact HBQuantifier.existentialElimination T H (claim etag vtag stag ptag ctag dtag index depth positive rest raw) ⟨hb⟩
theorem equalCase {n ctx : Nat} (p : Program n) (etag vtag stag ptag ctag atag dtag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩) (index depth positive rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal index depth) (claim etag vtag stag ptag ctag dtag index depth positive rest raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal index depth
 let V := RawReflexivityDispatcher.valid vtag raw
 let P := Formula.equal (HistoryDifference.differenceCall dtag index (.succ depth)) (.succ positive)
 let G := [P,V,E]
 have hh : Hilbert.Local T ctx G E := .hypothesis (by simp [G])
 have hv0 : Hilbert.Local T ctx G V := .hypothesis (by simp [G])
 obtain ⟨hequal⟩ := BranchProof.equalIndex p G etag vtag stag ptag ctag atag he hv hs hp hc ha depth rest raw hv0
 have hout := Hilbert.Local.mp (.mp (.base (transportIndex etag stag ptag ctag depth index depth rest raw))
  (HistoryOrder.StepProof.localSym _ _ hh)) hequal
 exact ⟨hout.discharge.discharge.discharge.finish⟩
theorem exactEmission : Targets.InternalIndexEmission := by
 intro n p etag vtag stag ptag ctag atag dtag he hv hs hp hc ha hd ctx index depth positive rest raw
 obtain ⟨hl⟩ := lower p etag vtag stag ptag ctag atag dtag he hv hs hp hc ha hd index depth positive rest raw
 obtain ⟨heq⟩ := equalCase p etag vtag stag ptag ctag atag dtag he hv hs hp hc ha hd index depth positive rest raw
 obtain ⟨hu⟩ := upper p etag vtag stag ptag ctag atag dtag he hv hs hp hc ha hd index depth positive rest raw
 obtain ⟨htri⟩ := HistoryCancellation.TrichotomyProof.trichotomy (GorbowPRNumeralCalculation.Theory p) index depth
 have hr := Derivation.mp (.mp (.logical (.orElim _ _ _)) heq) hu
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hr) htri⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.Proof
