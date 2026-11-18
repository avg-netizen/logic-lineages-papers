import LogicLineages.PersistentMarking.ProtectedSpineLawTargets
import LogicLineages.PersistentMarking.MarkedConstructorOperator

namespace LogicLineages.PersistentMarking.ProtectedSpineApplicationCounterexampleTargets
open Spine DecisionInventory DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter
open MarkedConstructorOperator (environment)

def source : Expr := .head .succ .nil
def target : Expr := .lam .ground (.free .ground 0)
def argument : Expr := .free .ground 0
def arguments : Args := .cons argument .nil
def result : Expr := .marked .succ .ground .nil arguments
def context : Context := [none]
def inputEnvironment : Environment := environment source target
def sourceHeads : List Head := (inventory source target).sourceHeads
def bottomFamily : Code := MarkedFamilyLattice.join inputEnvironment sourceHeads []

def interpreted (S : Signature) (q : Expr) : Code :=
  codeAt inputEnvironment q.type (evaluate S inputEnvironment sourceHeads bottomFamily q) context ⟨[],[]⟩

def helperOutput (S : Signature) : Code :=
  call S inputEnvironment sourceHeads bottomFamily source context [] [] [.ground] [interpreted S argument] .ground

/-- A genuine successful source call separates the two same-family readings. -/
def AvailabilityGap : Prop := ∀ S,
  PaperTerm S source (.arrow .ground .ground) ∧ Ordinary source ∧
  PaperTerm S target (.arrow .ground .ground) ∧ Ordinary target ∧
  WellFormed inputEnvironment.types inputEnvironment.ports context ∧
  bottomFamily ∈ MarkedFamilyCoherence.retained inputEnvironment sourceHeads ∧
  CallTyped EmptyContext source.type arguments .ground ∧
  apply source arguments = some result ∧
  (decode inputEnvironment .ground context (helperOutput S)).available context = false ∧
  (decode inputEnvironment .ground context (interpreted S result)).available context = true ∧
  helperOutput S ≠ interpreted S result

end LogicLineages.PersistentMarking.ProtectedSpineApplicationCounterexampleTargets
