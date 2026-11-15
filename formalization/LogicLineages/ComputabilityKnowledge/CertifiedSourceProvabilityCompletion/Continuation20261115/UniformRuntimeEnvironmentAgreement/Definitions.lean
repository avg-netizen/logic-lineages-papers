module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement
open GorbowSyntax SixSol20261113
/-- Remove the last in-scope variable (index depth), placing its replacement
at runtime coordinate zero. Existing closed coordinates shift by Fin.succ;
protected indices below depth retain their original de Bruijn positions. -/
def specialize {n depth inputs : Nat}
 (e : FixedFormulaSubstitution.Environment n (depth+1) inputs) :
 FixedFormulaSubstitution.Environment n depth (inputs+1) := fun i =>
 match e i with
 | .inl j => if h : j.val < depth then .inl ⟨j.val,h⟩ else .inr 0
 | .inr j => .inr j.succ
/-- Original formula task at the input depth, above arbitrary untouched rest. -/
def initial {ctx : Nat} (ptag ctag depth : Nat) (rest out : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (.succ (HistoryLookup.consCall ctag
  (LiteralSyntaxStep.taskCall ptag 1 (Term.numeral (depth+1))) rest)) out
/-- Full packed-state agreement, not just the output projection. Runtime
replacement is prepended to the existing raw vector and is not rescanned. -/
def agreement {n depth inputs ctx : Nat} (ftag ptag ctag atag : Nat)
 (e : FixedFormulaSubstitution.Environment n (depth+1) inputs) (f : Formula n)
 (raw : List.Vector (Term ctx) inputs) (replacement rest out : Term ctx) : Formula ctx :=
 .equal (UniformClosedSubstitutionRawFold.foldCall ftag
  (FixedFormulaSubstitution.formulaValue ctag atag raw f e)
  (initial ptag ctag depth rest out) replacement)
  (HistoryKernel.pairCall ptag (.succ rest)
   (HistoryAppend.appendCall atag out
    (FixedFormulaSubstitution.formulaValue ctag atag (List.Vector.cons replacement raw) f (specialize e))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement
