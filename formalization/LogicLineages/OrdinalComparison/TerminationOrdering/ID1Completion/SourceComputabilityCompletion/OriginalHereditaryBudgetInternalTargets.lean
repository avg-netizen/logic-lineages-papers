module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalMultiplicationLawsProof (mul)
/-- Literal numeric budget recursion, with input order [depth,branching]. -/
def Zero : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (branching : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget (suc z) z branching))
def Successor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (depth branching previous : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget previous depth branching)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget (suc (mul branching previous)) (suc depth) branching))
def SuccessorEquation : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (depth branching previous current : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget previous depth branching)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget current (suc depth) branching)) →
 Nonempty (Derivation body Delta (eqn current (suc (mul branching previous))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalTargets
