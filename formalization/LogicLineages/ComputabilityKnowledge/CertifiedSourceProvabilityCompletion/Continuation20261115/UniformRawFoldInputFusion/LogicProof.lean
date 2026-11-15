module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.LogicProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem substFusion {m n : Nat} (s : Fin m → Term n) ftag atag (left right packed raw : Term m) :
 substituteFormula s (fusion ftag atag left right packed raw) =
 fusion ftag atag (substitute s left) (substitute s right) (substitute s packed) (substitute s raw) := by
 simp only [fusion,substituteFormula,UniformClosedSubstitutionRawFold.foldCall,
  HistoryAppend.appendCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
def allStates {ctx : Nat} (ftag atag : Nat) (left right raw : Term ctx) : Formula ctx :=
 .all (fusion ftag atag (liftTerm left) (liftTerm right) (.var 0) (liftTerm raw))
theorem substAll {m n : Nat} (s : Fin m → Term n) ftag atag (left right raw : Term m) :
 substituteFormula s (allStates ftag atag left right raw) =
 allStates ftag atag (substitute s left) (substitute s right) (substitute s raw) := by
 simp only [allStates,substituteFormula,substFusion,HistoryOrder.SupportProof.substituteLift,
  substitute,liftSubstitute,Fin.cases_zero]
noncomputable def instanceRule {T : Sentence → Prop} {ctx : Nat} ftag atag (left right raw packed : Term ctx) :
 Derivation T (.imp (allStates ftag atag left right raw) (fusion ftag atag left right packed raw)) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (fusion ftag atag (liftTerm left) (liftTerm right) (.var 0) (liftTerm raw)) packed)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substFusion,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,allStates] using h
noncomputable def transportAll {T : Sentence → Prop} {ctx : Nat} ftag atag (a b right raw : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (allStates ftag atag a right raw) (allStates ftag atag b right raw))) := by
 have h := Derivation.logical (A := T) (.equalityReplace
  (allStates ftag atag (.var 0) (liftTerm right) (liftTerm raw)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substAll,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h

def bounded {ctx : Nat} (ftag atag : Nat) (bound right raw : Term ctx) : Formula ctx :=
 .all (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
  (allStates ftag atag (.var 0) (liftTerm right) (liftTerm raw)))
theorem substBounded {m n : Nat} (s : Fin m → Term n) ftag atag (bound right raw : Term m) :
 substituteFormula s (bounded ftag atag bound right raw) =
 bounded ftag atag (substitute s bound) (substitute s right) (substitute s raw) := by
 simp only [bounded,substituteFormula,HistoryBounds.SupportProof.substWeak,substAll,
  HistoryOrder.SupportProof.substituteLift,substitute,liftSubstitute,Fin.cases_zero]
noncomputable def boundedInstance {T : Sentence → Prop} {ctx : Nat} ftag atag (bound code right raw : Term ctx) :
 Derivation T (.imp (bounded ftag atag bound right raw)
  (.imp (HistoryBounds.weakBound code bound) (allStates ftag atag code right raw))) := by
 have h := Derivation.logical (A := T) (.allInstantiate
  (.imp (HistoryBounds.weakBound (.var 0) (liftTerm bound))
   (allStates ftag atag (.var 0) (liftTerm right) (liftTerm raw))) code)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substituteFormula,
  HistoryBounds.SupportProof.substWeak,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero,bounded] using h
noncomputable def inputCongruence {T : Sentence → Prop} {ctx : Nat} ftag (a b packed raw : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (UniformClosedSubstitutionRawFold.foldCall ftag a packed raw)
  (UniformClosedSubstitutionRawFold.foldCall ftag b packed raw)) := by
 apply Logic.callCongruence T ftag
 intro i
 cases i using Fin.cases with
 | zero => exact h
 | succ i => cases i using Fin.cases with
   | zero => exact .logical (.reflexive packed)
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive raw)
     | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.LogicProof
