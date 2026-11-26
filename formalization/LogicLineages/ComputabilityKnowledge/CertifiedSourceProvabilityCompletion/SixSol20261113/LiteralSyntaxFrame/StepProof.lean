module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepCons
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralSyntaxStep StepCons
open HistoryIteratorSuffix.WitnessProof

theorem weakenProperty {ctx : Nat} stag atag (tasks out suffix token : Term ctx) :
 GorbowPACore.weaken (property stag atag tasks out suffix token) =
 property stag atag (liftTerm tasks) (liftTerm out) (liftTerm suffix) (liftTerm token) := by
 rw [GorbowPACore.weaken,StepCons.substProperty]
 rfl

theorem positiveFrame {n ctx : Nat} (p : Program n) (stag etag atag ctag ltag rtag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (he : (nodes p)[etag]? = some ⟨2,expandCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryDecoder.decoder false⟩) (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (code out suffix token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property stag atag (.succ code) out suffix token)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let cp := ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 let Q := property stag atag (.succ code) out suffix token
 let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
 let C := liftTerm (liftTerm code)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall cp A B) C) := .hypothesis List.mem_cons_self
 obtain ⟨hcons0⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
 have hcons := localTrans _ _ _ (.base hcons0) (localUnary (.succ (.var 0)) _ _ hh)
 obtain ⟨hi⟩ := consFrame p stag etag atag ctag ltag rtag hs he ha hc hl hr A B
  (liftTerm (liftTerm out)) (liftTerm (liftTerm suffix)) (liftTerm (liftTerm token))
 have hout := Hilbert.Local.mp (.mp (.base (StepCons.transport stag atag _ _
  (liftTerm (liftTerm out)) (liftTerm (liftTerm suffix)) (liftTerm (liftTerm token)))) hcons) (.base hi)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,C,weakenProperty,liftTerm,renameTerm,substitute,Fin.cases_zero] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
 obtain ⟨hsurj⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
 exact ⟨.mp helim hsurj⟩

theorem emptyFrame {n ctx : Nat} (p : Program n) (stag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,stepCode⟩) (out suffix token : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property stag atag .zero out suffix token)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (stepCall stag (.succ .zero) token) (.succ out)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := LiteralSyntaxStep.StepProof.internalEmpty n p stag hs ctx token
 have bad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh) (.base hz)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.explosion _ bad (.base (.arithmetic (.succNotZero out)))))⟩

theorem internalStepFrame : Targets.InternalStepFrame := by
 intro n p stag atag ctag ltag rtag hs ha hc hl hr ctx tasks out suffix token
 obtain ⟨etag,he⟩ := StepCases.expandInstalled p stag hs
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property stag atag tasks out suffix token
 let E := Formula.equal tasks .zero
 obtain ⟨hz⟩ := emptyFrame p stag atag hs out suffix token
 have he0 : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (StepCons.transport stag atag .zero tasks out suffix token)) (HistoryOrder.StepProof.localSym _ _ he0)) (.base hz)))
 let H := HistoryOrder.SupportProof.predBody tasks
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm tasks) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := positiveFrame p stag etag atag ctag ltag rtag hs he ha hc hl hr (.var (0 : Fin (ctx+1))) (liftTerm out) (liftTerm suffix) (liftTerm token)
 have hout := Hilbert.Local.mp (.mp (.base (StepCons.transport stag atag _ _ (liftTerm out) (liftTerm suffix) (liftTerm token))) (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenProperty] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hp⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hsplit⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T tasks
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hp) hsplit⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.StepProof
