module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepConsSuccessProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepInstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open StepConsSuccessProof HistoryIteratorSuffix.WitnessProof

/-- Positive raw stack codes are internally decomposed using original pair
surjectivity at the cons program's actual child tag. No native decoding occurs. -/
theorem positive {n ctx : Nat} (p : Program n) (s e c a : Nat)
 (hs : (nodes p)[s]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[e]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩) (code tok result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property s e c a (.succ code) tok result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let cp := c + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hcp := Equations.argumentChild p c .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 let Q := property s e c a (.succ code) tok result
 let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
 let C := liftTerm (liftTerm code)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall cp A B) C) :=
  .hypothesis List.mem_cons_self
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p c hc (ctx+2) A B
 have hrow := localTrans _ _ _ (.base hcons) (localUnary (.succ (.var 0)) _ _ hh)
 obtain ⟨hi⟩ := StepConsSuccessProof.cons p s e c a hs he hc ha A B
  (liftTerm (liftTerm tok)) (liftTerm (liftTerm result))
 have hout := Hilbert.Local.mp (.mp (.base (transport s e c a _ _
  (liftTerm (liftTerm tok)) (liftTerm (liftTerm result)))) hrow) (.base hi)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,C,weakenProperty,liftTerm,renameTerm,substitute] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
 obtain ⟨hsurj⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
 exact ⟨.mp helim hsurj⟩

/-- Internal zero/successor split completes inversion for every raw stack code. -/
theorem allStacks {n ctx : Nat} (p : Program n) (s e c a : Nat)
 (hs : (nodes p)[s]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[e]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩) (code tok result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property s e c a code tok result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property s e c a code tok result
 let E := Formula.equal code .zero
 have hzero : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 obtain ⟨hz⟩ := StepConsSuccessProof.empty p s e c a hs tok result
 have hout := Hilbert.Local.mp (.mp (.base (transport s e c a .zero code tok result))
  (HistoryOrder.StepProof.localSym _ _ hzero)) (.base hz)
 have hzcase : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge hout)
 let H := HistoryOrder.SupportProof.predBody code
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm code) (.succ (.var 0))) :=
  .hypothesis List.mem_cons_self
 obtain ⟨hpositive⟩ := positive p s e c a hs he hc ha (.var (0 : Fin (ctx+1))) (liftTerm tok) (liftTerm result)
 have hpos := Hilbert.Local.mp (.mp (.base (transport s e c a _ _ (liftTerm tok) (liftTerm result)))
  (HistoryOrder.StepProof.localSym _ _ hh)) (.base hpositive)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenProperty] using Hilbert.Local.finish (Hilbert.Local.discharge hpos)
 obtain ⟨hpcase⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T code
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzcase) hpcase) hcases⟩

theorem stepSuccessDecomposition : StepSuccessTargets.InternalStepSuccessDecomposition := by
 intro n p s e c a hs he hc ha ctx tasks tok result
 exact allStacks p s e c a hs he hc ha tasks tok result
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepSuccessProof
