module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportWitnessProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open StepTransportTargets SubstitutionProof HistoryOrder.SupportProof

theorem substBody {m n : Nat} (s : Fin m → Term n) stag len q l r (nt tok oldResult newResult : Term m) :
 substituteFormula s (witnessBody stag len q l r nt tok oldResult newResult) =
 witnessBody stag len q l r (substitute s nt) (substitute s tok)
  (substitute s oldResult) (substitute s newResult) := by
 simp only [witnessBody,substituteFormula,substStack,LiteralSyntaxStep.stepCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem bodyAt {ctx : Nat} stag len q l r (nt tok oldResult newResult : Term ctx) :
 GorbowStandardInstances.instantiate
  (witnessBody stag len q l r (liftTerm nt) (liftTerm tok) (liftTerm oldResult) (.var 0)) newResult =
 witnessBody stag len q l r nt tok oldResult newResult := by
 simp only [GorbowStandardInstances.instantiate,substBody,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def witnessIntro {T : Sentence → Prop} {ctx : Nat} stag len q l r
 (nt tok oldResult newResult : Term ctx) :
 Derivation T (.imp (witnessBody stag len q l r nt tok oldResult newResult)
  (witnesses stag len q l r nt tok oldResult)) := by
 have h := existsIntroRule (T := T)
  (witnessBody stag len q l r (liftTerm nt) (liftTerm tok) (liftTerm oldResult) (.var 0)) newResult
 rw [bodyAt] at h
 exact h
theorem substWitnesses {m n : Nat} (s : Fin m → Term n) stag len q l r (nt tok oldResult : Term m) :
 substituteFormula s (witnesses stag len q l r nt tok oldResult) =
 witnesses stag len q l r (substitute s nt) (substitute s tok) (substitute s oldResult) := by
 simp only [witnesses,substituteFormula,substBody,substituteLift,substitute,liftSubstitute,Fin.cases_zero]
/-- The residual implication consumed while eliminating old-stack witnesses. -/
def property {ctx : Nat} (stag len q l r : Nat) (ot nt tok result : Term ctx) : Formula ctx :=
 .imp (stackRelation len q l r ot nt)
  (.imp (.equal (LiteralSyntaxStep.stepCall stag (.succ ot) tok) (.succ result))
   (witnesses stag len q l r nt tok result))
theorem substProperty {m n : Nat} (s : Fin m → Term n) stag len q l r (ot nt tok result : Term m) :
 substituteFormula s (property stag len q l r ot nt tok result) =
 property stag len q l r (substitute s ot) (substitute s nt) (substitute s tok) (substitute s result) := by
 simp only [property,substituteFormula,substStack,substWitnesses,LiteralSyntaxStep.stepCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenProperty {ctx : Nat} stag len q l r (ot nt tok result : Term ctx) :
 GorbowPACore.weaken (property stag len q l r ot nt tok result) =
 property stag len q l r (liftTerm ot) (liftTerm nt) (liftTerm tok) (liftTerm result) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportWitnessProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportWitnessProof
