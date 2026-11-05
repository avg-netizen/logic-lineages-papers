module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanup
open NormalForm

/-- Keep the actual occurrence-name list, including repetitions. -/
def linearNames (p : Formula) : List Nat := p.variables.filter (fun i => LinearRows.isLinear i p)
def cleanup (p : Formula) : Formula := LinearBlock.eliminate (linearNames p) p
/-- Existential closure of the original raw-name valuation, used only as semantics. -/
def Satisfiable (p : Formula) : Prop := ∃ ν : Nat → Nat, p.eval ν

namespace Code
def linearNames (code : Nat) : List Nat :=
  (MaximalPlainBranchPrograms.Code.variables code).filter (fun i => LinearRows.Code.isLinear i code)
def cleanup (code : Nat) : Nat := LinearBlock.Code.eliminate (linearNames code) code
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanup
