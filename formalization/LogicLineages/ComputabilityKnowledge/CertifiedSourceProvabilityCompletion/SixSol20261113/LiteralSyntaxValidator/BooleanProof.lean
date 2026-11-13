module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.BooleanProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph FormulaBindingProof

theorem internalBoolean : Targets.InternalBoolean := by
 intro n p vtag hv ctx context raw
 let T := GorbowPRNumeralCalculation.Theory p
 obtain ⟨stag,ptag,ctag,etag,hs,hp,hc,he⟩ := nodesInstalled p vtag hv
 let result := LiteralSyntaxScan.scanCall stag (taskList ptag ctag context) raw
 let equality := HistoryKernel.pairCall etag result (.succ .zero)
 obtain ⟨hb⟩ := binding p vtag stag ptag ctag etag hv hs hp hc he context raw
 obtain ⟨hr⟩ := HistoryKernel.RangeProof.equalRange p etag he result (.succ .zero)
 let phi : Formula (ctx+1) := .disj (.equal (.var 0) .zero) (.equal (.var 0) (.succ .zero))
 have ht := Derivation.logical (A := T) (.equalityReplace phi equality (formulaCall vtag context raw))
 have ht' : Derivation T (.imp (.equal equality (formulaCall vtag context raw))
  (.imp (.disj (.equal equality .zero) (.equal equality (.succ .zero)))
   (.disj (.equal (formulaCall vtag context raw) .zero) (.equal (formulaCall vtag context raw) (.succ .zero))))) := by
  simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,phi,substituteFormula,substitute,Fin.cases_zero] using ht
 exact ⟨.mp (.mp ht' (Support.equalitySymmetry _ _ hb)) hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.BooleanProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.BooleanProof
