module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TagSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution PrescribedRuntimeEquality
open GorbowSubstitution
/-- Remove only the last runtime-tag coordinate. First n variables remain open. -/
def plug : (n : Nat) → Nat → Fin (n+1) → Term n
 | 0, tag => fun _ => Term.numeral tag
 | n+1, tag => liftSubstitute (plug n tag)
theorem plugCast (n tag : Nat) (i : Fin n) : plug n tag i.castSucc = .var i := by
 induction n with
 | zero => exact Fin.elim0 i
 | succ n ih =>
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
   change renameTerm Fin.succ (plug n tag i.castSucc) = _
   rw [ih]
   rfl
theorem plugLast (n tag : Nat) : plug n tag (Fin.last n) = Term.numeral tag := by
 induction n with
 | zero => rfl
 | succ n ih =>
  change renameTerm Fin.succ (plug n tag (Fin.last n)) = _
  rw [ih]
  exact GorbowHeaderSubstitutionProof.numerals n (n+1) (fun i => .var i.succ) tag

def join {n : Nat} (tag : Nat) (sigma : Fin n → Term 0) : Fin (n+1) → Term 0 :=
 Fin.lastCases (Term.numeral tag) sigma
theorem full {n : Nat} (tag : Nat) (sigma : Fin n → Term 0) :
 (fun i => substitute sigma (plug n tag i)) = join tag sigma := by
 funext i
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [plugLast,join,Fin.lastCases_last,SixSol20261112.Fuel.Logic.substNumeral]
 · simp only [plugCast,join,Fin.lastCases_castSucc,substitute]
theorem tail {n : Nat} (tag : Nat) (sigma : Fin (n+1) → Term 0) (i : Fin (n+1)) :
 join tag sigma i.succ = join tag (fun j => sigma j.succ) i := by
 refine Fin.lastCases ?_ (fun j => ?_) i
 · change join tag sigma (Fin.last (n+1)) = _
   simp only [join,Fin.lastCases_last]
 · change join tag sigma j.succ.castSucc = _
   simp only [join,Fin.lastCases_castSucc]
theorem head {n : Nat} (tag : Nat) (sigma : Fin (n+1) → Term 0) : join tag sigma 0 = sigma 0 := by
 change join tag sigma (Fin.castSucc (0 : Fin (n+1))) = _
 simp only [join,Fin.lastCases_castSucc]

theorem formulaFull {n : Nat} (tag : Nat) (f : Formula (n+1)) (sigma : Fin n → Term 0) :
 substituteFormula sigma (substituteFormula (plug n tag) f) = substituteFormula (join tag sigma) f := by
 rw [GorbowFormulaCompositionProof.composition,full]
theorem formulaHead {n : Nat} (tag : Nat) (f : Formula (n+2)) (sigma : Fin n → Term 0) :
 substituteFormula (liftSubstitute sigma) (substituteFormula (plug (n+1) tag) f) =
 substituteFormula (liftSubstitute (join tag sigma)) f := by
 rw [GorbowFormulaCompositionProof.composition]
 change substituteFormula (fun i => substitute (liftSubstitute sigma) (liftSubstitute (plug n tag) i)) f = _
 rw [GorbowFormulaCompositionProof.liftComposition,full]

theorem root (m tag : Nat) : substituteFormula (plug m tag) (rootTemplate m) = CurrentRecursionBaseCertificate.rootFormula m tag := by
 let xs := List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))
 have hx : xs.map (substitute (plug m tag)) = argumentVariables m := by
  ext i
  simp only [xs,List.Vector.get_map,List.Vector.get_ofFn,substitute,plugCast,argumentVariables]
 dsimp only [xs] at hx
 simp only [rootTemplate,openCall,substituteFormula,substitute,
  CurrentCalculationFormulaProgram.NativeProof.substPair,CurrentCalculationFormulaProgram.NativeProof.substTuple,
  SixSol20261112.Fuel.Logic.substNumeral,plugLast,← List.Vector.toList_map,List.Vector.map_cons,hx,
  CurrentRecursionBaseCertificate.rootFormula,call,GorbowRegistryTuple.headerTerm]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TagSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TagSyntax
