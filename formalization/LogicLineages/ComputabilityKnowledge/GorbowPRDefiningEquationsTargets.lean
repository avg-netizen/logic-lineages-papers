module

public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry

def HeaderCalibration : Prop := ∀ n (p : Program n) (tag : Nat) m (q : Program m)
    (args : List Nat) (h : args.length = m),
  (nodes p)[tag]? = some ⟨m,q⟩ →
    functionProgram p (GorbowRegistryTuple.header m tag args) = evaluate q ⟨args,h⟩

def TermCalibration : Prop := ∀ ctx n (p : Program n) (tag : Nat) m (q : Program m)
    (args : List.Vector (Term ctx) m) I (rho : Fin ctx → Nat),
  (nodes p)[tag]? = some ⟨m,q⟩ →
    (call tag args).realize (interpretation p I) rho =
      evaluate q (args.map fun t => t.realize (interpretation p I) rho)

def NodeEquationsSound : Prop := ∀ n (p : Program n) (tag : Nat) (a : Packed),
  (nodes p)[tag]? = some a → ∀ I sigma, sigma ∈ nodeEquations a.2 tag →
    sigma.realize (interpretation p I) Fin.elim0

def AllAxiomsSound : Prop := ∀ n (p : Program n) I sigma,
  sigma ∈ axioms p → sigma.realize (interpretation p I) Fin.elim0

def CheckExact : Prop := ∀ n (p : Program n) raw,
  check p raw = true ↔ ∃ sigma ∈ axioms p, GorbowFormulaPrefixCode.encode sigma = raw

def FixedCheckerPrimitive : Prop := ∀ n (p : Program n), Primrec (check p)

def TheorySoundness : Prop := ∀ n (p : Program n) sigma,
  GorbowTheoryProof.Derivation (fun tau => tau ∈ axioms p) sigma →
    ∀ I, sigma.realize (interpretation p I) Fin.elim0

end LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.Targets
