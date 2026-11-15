module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof
open GorbowFormulaSubstitution

theorem closedEncode (depth : Nat) (u : Term 0) :
 GorbowTermPrefixCode.encode (renameTerm (Fin.elim0 : Fin 0 → Fin depth) u) = GorbowTermPrefixCode.encode u := by
 induction u with
 | var i => exact Fin.elim0 i
 | zero => rfl
 | succ t ih => simp_all [renameTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
 | add t v ht hv => simp_all [renameTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
 | mul t v ht hv => simp_all [renameTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
 | universalFunction t ih => simp_all [renameTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]

theorem closedLift (depth : Nat) (u : Term 0) :
 renameTerm Fin.succ (renameTerm (Fin.elim0 : Fin 0 → Fin depth) u) =
 renameTerm (Fin.elim0 : Fin 0 → Fin (depth+1)) u := by
 induction u with
 | var i => exact Fin.elim0 i
 | zero => rfl
 | succ t ih => simp_all [renameTerm,GorbowSubstitution.substitute]
 | add t v ht hv => simp_all [renameTerm,GorbowSubstitution.substitute]
 | mul t v ht hv => simp_all [renameTerm,GorbowSubstitution.substitute]
 | universalFunction t ih => simp_all [renameTerm,GorbowSubstitution.substitute]

theorem assignmentLift {n depth inputs : Nat} (e : Environment n depth inputs) (u : Fin inputs → Term 0) :
 assignment (liftEnvironment e) u = liftSubstitute (assignment e u) := by
 funext i
 refine Fin.cases ?_ (fun j => ?_) i
 · rfl
 · cases h : e j with
   | inl v => simp [assignment,liftEnvironment,liftSubstitute,h,renameTerm,GorbowSubstitution.substitute]
   | inr v => simpa [assignment,liftEnvironment,liftSubstitute,h] using (closedLift depth (u v)).symm

theorem nativeTerm : Targets.NativeTerm := by
 intro n depth inputs e t u
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 induction t with
 | var i =>
  cases h : e i with
  | inl j => simp [termProgram,assignment,h,constantEval,GorbowSubstitution.substitute]
  | inr j => simp [termProgram,assignment,h,rawInputs,evaluate,GorbowSubstitution.substitute,closedEncode]
 | zero => rfl
 | succ t ih =>
  simp only [termProgram,unary,twoEval,constantEval,ih,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl
 | add t v ht hv =>
  simp only [termProgram,binary,unary,twoEval,constantEval,ht,hv,appendList,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl
 | mul t v ht hv =>
  simp only [termProgram,binary,unary,twoEval,constantEval,ht,hv,appendList,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl
 | universalFunction t ih =>
  simp only [termProgram,unary,twoEval,constantEval,ih,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl

theorem nativeFormula : Targets.NativeFormula := by
 intro n depth inputs e f u
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 induction f generalizing depth with
 | equal t v =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm _ _ _ e t u,nativeTerm _ _ _ e v u,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode]
  rfl
 | universalRelation t =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm _ _ _ e t u,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode]
  rfl
 | agent t =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm _ _ _ e t u,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode]
  rfl
 | knowledgeAll t =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm _ _ _ e t u,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode]
  rfl
 | knowledge t v =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm _ _ _ e t u,nativeTerm _ _ _ e v u,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode]
  rfl
 | truth t =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm _ _ _ e t u,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode]
  rfl
 | neg f ih =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode,ih]
  rfl
 | imp f g hf hg =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode,hf,hg]
  rfl
 | conj f g hf hg =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode,hf,hg]
  rfl
 | disj f g hf hg =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode,hf,hg]
  rfl
 | all f ih =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode,← assignmentLift,ih]
  rfl
 | ex f ih =>
  simp only [formulaProgram,binary,unary,twoEval,constantEval,nativeTerm,appendList,hc,GorbowFormulaSubstitution.substituteFormula,GorbowFormulaPrefixCode.encode,← assignmentLift,ih]
  rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.NativeProof
