module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.InductionSupport
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def property {ctx m : Nat} (ctag ftag ptag : Nat) (value index fuel : Term ctx) (params : List.Vector (Term ctx) m) : Formula ctx :=
 core ctag index fuel (familyCall ftag value params) (familyCall ptag value params)

theorem substProperty {a b m : Nat} (sub : Fin a → Term b) ctag ftag ptag (value index fuel : Term a) (params : List.Vector (Term a) m) :
 substituteFormula sub (property ctag ftag ptag value index fuel params) =
 property ctag ftag ptag (substitute sub value) (substitute sub index) (substitute sub fuel) (params.map (substitute sub)) := by
 simp only [property,core,LiteralCheckerAcceptance.coreCall,familyCall,substituteFormula,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem cancelParams {ctx m : Nat} (out : Term ctx) (params : List.Vector (Term ctx) m) :
 (params.map liftTerm).map (substitute (Fin.cases out Term.var)) = params := by
 ext i
 simp only [List.Vector.get_map,liftTerm,Support.shiftCancel]

theorem successorParams {ctx m : Nat} (params : List.Vector (Term ctx) m) :
 (params.map liftTerm).map (substitute (Fin.cases (.succ (.var 0)) (fun i : Fin ctx => Term.var i.succ))) = params.map liftTerm := by
 ext i
 simp only [List.Vector.get_map,successorLift]

theorem fromBaseStep {T : Sentence → Prop} {ctx m : Nat} ctag ftag ptag
 (value index fuel : Term ctx) (params : List.Vector (Term ctx) m)
 (hz : Derivation T (property ctag ftag ptag .zero index fuel params))
 (hs0 : Derivation T (.imp
  (property ctag ftag ptag (.var 0 : Term (ctx+1)) (liftTerm index) (liftTerm fuel) (params.map liftTerm))
  (property ctag ftag ptag (.succ (.var 0)) (liftTerm index) (liftTerm fuel) (params.map liftTerm)))) :
 Nonempty (Derivation T (property ctag ftag ptag value index fuel params)) := by
 let phi : Formula (ctx+1) := property ctag ftag ptag (.var 0) (liftTerm index) (liftTerm fuel) (params.map liftTerm)
 have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
  simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,
   liftTerm,Support.shiftCancel,Fin.cases_zero,cancelParams,successorParams] using hz
 have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
  simpa only [phi,GorbowStandardInduction.successorInstance,substProperty,substitute,
   successorLift,Fin.cases_zero,Support.shiftCancel,cancelParams,successorParams] using hs0
 have h := atTerm phi value (induction phi hb hs)
 exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substProperty,substitute,
  liftTerm,Support.shiftCancel,Fin.cases_zero,cancelParams,successorParams] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.InductionSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.InductionSupport
