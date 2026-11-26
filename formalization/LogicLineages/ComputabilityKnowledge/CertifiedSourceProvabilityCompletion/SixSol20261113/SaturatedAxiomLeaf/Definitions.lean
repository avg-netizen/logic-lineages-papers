module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.InductionStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector
open SixSol20261112
/-- Five-input checker interface [index,fuel,context,formula,certificate].
The original axiom leaf sees precisely [index,fuel,encoded line]; unused
context/formula parameters are ignored, never inspected or decoded. -/
def liftArguments : Fin 3 → Program 5 :=
 Fin.cases (.projection 0) (Fin.cases (.projection 1) (Fin.cases (.projection 4) Fin.elim0))
def lifted (x : Program 3) : Program 5 := .composition x liftArguments
/-- Original three-input order is [index,fuel,encoded line]. Both unused
checker fields are literal zero, so every malformed line/default is retained. -/
def wrapperArguments : Fin 5 → Program 3 :=
 Fin.cases (.projection 0) (Fin.cases (.projection 1)
  (Fin.cases (Fuel.zeroProgram 3) (Fin.cases (Fuel.zeroProgram 3)
   (Fin.cases (.projection 2) Fin.elim0))))
/-- Explicit bounded saturation of an arbitrary axiom leaf. Semantic
calibration and internal source monotonicity are independent obligations. -/
def saturated (x : Program 3) : Program 3 := .composition (Fuel.verifier (lifted x)) wrapperArguments

def leafCall {ctx : Nat} (tag : Nat) (index fuel line : Term ctx) : Term ctx :=
 call tag (index ::ᵥ fuel ::ᵥ line ::ᵥ nil)
def success {ctx : Nat} (tag : Nat) (index fuel line : Term ctx) : Formula ctx :=
 .equal (leafCall tag index fuel line) (.succ .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf
