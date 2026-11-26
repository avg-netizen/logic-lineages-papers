module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NewStackProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStackProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open GorbowSubstitution GorbowFormulaSubstitution SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport BoundProof InvariantProof

def claim {ctx : Nat} (ftag stag ptag ctag atag len q l r : Nat)
 (tok tokens raw oldTasks newTasks rest out : Term ctx) : Formula ctx :=
 .imp (allStates ftag stag ptag ctag atag len q l r tokens raw)
  (property ftag stag ptag ctag atag len q l r (HistoryLookup.consCall ctag tok tokens) raw oldTasks newTasks rest out)
theorem substClaim {m n : Nat} (s : Fin m → Term n) ftag stag ptag ctag atag len q l r
 (tok tokens raw oldTasks newTasks rest out : Term m) :
 substituteFormula s (claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out) =
 claim ftag stag ptag ctag atag len q l r (substitute s tok) (substitute s tokens) (substitute s raw)
  (substitute s oldTasks) (substitute s newTasks) (substitute s rest) (substitute s out) := by
 simp only [claim,substituteFormula,substAllStates,InvariantProof.substProperty,HistoryLookup.DropEquationsProof.substCons]
theorem weakenClaim {ctx : Nat} ftag stag ptag ctag atag len q l r
 (tok tokens raw oldTasks newTasks rest out : Term ctx) :
 GorbowPACore.weaken (claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out) =
 claim ftag stag ptag ctag atag len q l r (liftTerm tok) (liftTerm tokens) (liftTerm raw)
  (liftTerm oldTasks) (liftTerm newTasks) (liftTerm rest) (liftTerm out) := by
 rw [GorbowPACore.weaken,substClaim]
 rfl
/-- Actual original step witnesses, including the expansion witness, are eliminated. -/
theorem eliminate {n ctx : Nat} (p : Program n)
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
 (tok tokens raw oldTasks newTasks rest out result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (StepSuccessTargets.witnesses xtag ctag atag oldTasks tok result)
   (claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := claim ftag stag ptag ctag atag len q l r tok tokens raw oldTasks newTasks rest out
 let H := StepWitnessProof.addedBody xtag ctag atag
  (liftTerm (liftTerm oldTasks)) (liftTerm (liftTerm tok)) (liftTerm (liftTerm result))
  (.var (1 : Fin (ctx+2))) (.var 0)
 let OT := liftTerm (liftTerm (liftTerm oldTasks))
 let NT := liftTerm (liftTerm (liftTerm newTasks))
 let TOK := liftTerm (liftTerm (liftTerm tok))
 let TOKENS := liftTerm (liftTerm (liftTerm tokens))
 let RAW := liftTerm (liftTerm (liftTerm raw))
 let REST := liftTerm (liftTerm (liftTerm rest))
 let OUT := liftTerm (liftTerm (liftTerm out))
 let A : Term (ctx+3) := .var 2
 let B : Term (ctx+3) := .var 1
 let C : Term (ctx+3) := .var 0
 let INPUT := HistoryLookup.consCall ctag TOK TOKENS
 let IH := allStates ftag stag ptag ctag atag len q l r TOKENS RAW
 let ENT := EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) OT
 let REL := stackRelation len q l r OT NT
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag OT INPUT) (.succ .zero)
 let G := [S,REL,ENT,IH,H]
 have hw : Hilbert.Local T (ctx+3) G H := .hypothesis (by simp [G])
 have heq := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hw
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hw
 have hex := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have hih : Hilbert.Local T (ctx+3) G IH := .hypothesis (by simp [G])
 have hent : Hilbert.Local T (ctx+3) G ENT := .hypothesis (by simp [G])
 have hrel : Hilbert.Local T (ctx+3) G REL := .hypothesis (by simp [G])
 have hscan : Hilbert.Local T (ctx+3) G S := .hypothesis (by simp [G])
 have hconsrel := Hilbert.Local.mp (.mp (.base (FinitePrefixProof.stackLeft len q l r
  OT (HistoryLookup.consCall ctag A B) NT)) heq) hrel
 obtain ⟨hnew⟩ := RelatedConsProof.relatedCons n p len q l r ctag hlen hq hc (ctx+3) A B NT
 have hneww := Hilbert.Local.mp (.base hnew) hconsrel
 obtain ⟨helim⟩ := NewStackProof.eliminate p ftag stag stepTag etag xtag ptag ctag atag len q l r
  hf hs hst he hx hp hc ha hlen hq hl hr dtag hd A B NT TOK TOKENS RAW REST OUT C
 have hcanonical := Hilbert.Local.mp (.mp (.mp (.base helim) hneww) hih) hex
 have hproperty := Hilbert.Local.mp (.mp (.base (TransportProof.oldTasks ftag stag ptag ctag atag len q l r
  INPUT RAW (HistoryLookup.consCall ctag A B) OT NT REST OUT))
  (HistoryOrder.StepProof.localSym _ _ heq)) hcanonical
 have hout := Hilbert.Local.mp (.mp (.mp hproperty hent) hrel) hscan
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken (GorbowPACore.weaken Q)))) := by
  dsimp only [Q]
  rw [weakenClaim,weakenClaim,weakenClaim]
  simpa only [claim,InvariantProof.property,OT,NT,TOK,TOKENS,RAW,REST,OUT,INPUT,IH,ENT,REL,S,G] using
   hout.discharge.discharge.discharge.discharge.discharge.finish
 obtain ⟨hadded⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken (GorbowPACore.weaken Q)) ⟨hb⟩
 obtain ⟨htail⟩ := HBQuantifier.existentialElimination T
  (StepWitnessProof.tailBody xtag ctag atag (liftTerm oldTasks) (liftTerm tok) (liftTerm result) (.var (0 : Fin (ctx+1))))
  (GorbowPACore.weaken Q) ⟨hadded⟩
 exact HBQuantifier.existentialElimination T
  (StepWitnessProof.headBody xtag ctag atag oldTasks tok result) Q ⟨htail⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStackProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.OldStackProof
