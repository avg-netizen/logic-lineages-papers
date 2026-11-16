module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

/-- Raw substitution coordinates: computed result, runtime node tag, inputs.
The node tag remains a runtime value, so building this AST precedes and does
not circularly depend on choosing its registry address. -/
def template (m : Nat) : Formula (m+2) :=
 .equal (.universalFunction (pairTerm (Term.numeral m)
  (pairTerm (.var 1) (tupleTerm (List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ : Term (m+2)))).toList)))) (.var 0)
def environment (m : Nat) : FixedFormulaSubstitution.Environment (m+2) 0 (m+2) := fun i => .inr i
/-- Runtime inputs: target tag followed by the original program's numeric inputs. -/
def tailProgram {m : Nat} (q : Program m) : Program (m+1) :=
 .composition q (fun i => .projection i.succ)
def arguments {m : Nat} (q : Program m) : Fin (m+2) → Program (m+1) :=
 Fin.cases (.composition LiteralNumeralPrefix.numeralCode (fun _ => tailProgram q))
  (fun i => .composition LiteralNumeralPrefix.numeralCode (fun _ => .projection i))
def program {m : Nat} (q : Program m) : Program (m+1) :=
 .composition (FixedFormulaSubstitution.formulaProgram (template m) (environment m)) (arguments q)
/-- Only the three codec addresses are used by callValue. -/
def codecTags (ctag atag ntag : Nat) : Tags := ⟨0,ctag,atag,0,0,0,ntag⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCalculationFormulaProgram
