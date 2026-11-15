module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepWitnessProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepRejectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepConsSuccessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open StepSuccessTargets StepWitnessProof

def property {ctx : Nat} (s e c a : Nat) (tasks tok result : Term ctx) : Formula ctx :=
 .imp (.equal (LiteralSyntaxStep.stepCall s (.succ tasks) tok) (.succ result)) (witnesses e c a tasks tok result)
theorem substProperty {m n : Nat} (sub : Fin m → Term n) s e c a (tasks tok result : Term m) :
 substituteFormula sub (property s e c a tasks tok result) =
 property s e c a (substitute sub tasks) (substitute sub tok) (substitute sub result) := by
 simp only [property,substituteFormula,substWitnesses,LiteralSyntaxStep.stepCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenProperty {ctx : Nat} s e c a (tasks tok result : Term ctx) :
 GorbowPACore.weaken (property s e c a tasks tok result) =
 property s e c a (liftTerm tasks) (liftTerm tok) (liftTerm result) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} s e c a (x y tok result : Term ctx) :
 Derivation T (.imp (.equal x y) (.imp (property s e c a x tok result) (property s e c a y tok result))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property s e c a (.var 0) (liftTerm tok) (liftTerm result)) x y)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substProperty,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

theorem empty {n ctx : Nat} (p : Program n) (s e c a : Nat)
 (hs : (nodes p)[s]? = some ⟨2,LiteralSyntaxStep.stepCode⟩) (tok result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property s e c a .zero tok result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let S := Formula.equal (LiteralSyntaxStep.stepCall s (.succ .zero) tok) (.succ result)
 have hh : Hilbert.Local T ctx [S] S := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := LiteralSyntaxStep.StepProof.internalEmpty n p s hs ctx tok
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh) (.base he)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (Hilbert.Local.explosion (witnesses e c a .zero tok result) hbad (.base (.arithmetic (.succNotZero result)))))⟩

/-- Invert an original successful cons-state step by internally splitting its
actual expansion call, rejecting NONE and introducing all three witnesses. -/
theorem cons {n ctx : Nat} (p : Program n) (s e c a : Nat)
 (hs : (nodes p)[s]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[e]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩) (head tail tok result : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (property s e c a (HistoryLookup.consCall c head tail) tok result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let row := HistoryLookup.consCall c head tail
 let X := LiteralSyntaxStep.expandCall e head tok
 let Z := Formula.equal X .zero
 let Q := property s e c a row tok result
 let S := Formula.equal (LiteralSyntaxStep.stepCall s (.succ row) tok) (.succ result)
 have hz : Hilbert.Local T ctx [S,Z] Z := .hypothesis (by simp)
 have hh : Hilbert.Local T ctx [S,Z] S := .hypothesis List.mem_cons_self
 obtain ⟨hzero⟩ := StepRejectionProof.stepReject p [S,Z] e c he hc head tail tok hz s hs
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh) hzero
 have hzeroCase : Derivation T (.imp Z Q) := Hilbert.Local.finish
  (Hilbert.Local.discharge (Hilbert.Local.discharge
   (Hilbert.Local.explosion (witnesses e c a row tok result) hbad (.base (.arithmetic (.succNotZero result))))))
 let H := HistoryOrder.SupportProof.predBody X
 let LS := Formula.equal (LiteralSyntaxStep.stepCall s (.succ (HistoryLookup.consCall c (liftTerm head) (liftTerm tail))) (liftTerm tok)) (.succ (liftTerm result))
 have hh' : Hilbert.Local T (ctx+1) [LS,H] LS := .hypothesis List.mem_cons_self
 have hg : Hilbert.Local T (ctx+1) [LS,H]
  (.equal (LiteralSyntaxStep.expandCall e (liftTerm head) (liftTerm tok)) (.succ (.var 0))) := by
  have h : Hilbert.Local T (ctx+1) [LS,H] H := .hypothesis (by simp)
  simpa only [H,X,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,
   LiteralSyntaxStep.expandCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil] using h
 obtain ⟨hpre⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p s e c a hs he hc ha (ctx+1)
  (liftTerm head) (liftTerm tail) (liftTerm tok) (.var 0)
 have hv := Hilbert.Local.mp (.base hpre) hg
 have hr := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _)))
  (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hh') hv)
 have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _)))
  (.base (.logical (.reflexive (HistoryLookup.consCall c (liftTerm head) (liftTerm tail))))))
  (.mp (.mp (.base (.logical (.andIntro _ _))) hg) hr)
 have hw := Hilbert.Local.mp (.base (witnessIntro e c a
  (HistoryLookup.consCall c (liftTerm head) (liftTerm tail)) (liftTerm tok) (liftTerm result)
  (liftTerm head) (liftTerm tail) (.var 0))) hb
 have hbody : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  rw [show Q = property s e c a row tok result from rfl,weakenProperty]
  simpa only [row,property,LS,liftTerm,renameTerm,HistoryLookup.DropEquationsProof.substCons] using
   Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hw))
 obtain ⟨hpositive⟩ := HBQuantifier.existentialElimination T H Q ⟨hbody⟩
 obtain ⟨hcases⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T X
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzeroCase) hpositive) hcases⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepConsSuccessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepConsSuccessProof
