module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifier
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB List.Vector

/-- Concrete intensional recursion: gate(0,x)=0 and gate(k+1,x)=x. -/
def gate : Program 2 :=
  .recursion GorbowNamedInternalProvability.zeroUnary (.projection (2 : Fin 3))

def arguments (q0 : Program 5) : Fin 2 → Program 5 :=
  Fin.cases (.projection (4 : Fin 5)) (fun _ => q0)

/-- A literal PR implementation of the SAME numeric checker, with its
canonical empty-certificate rejection made an explicit source AST branch.
This program is selected before the source c/rho fixed point is formed. -/
def verifier (q0 : Program 5) : Program 5 := .composition gate (arguments q0)

def input {ctx : Nat} (index fuel context formula certificate : Term ctx) :
    List.Vector (Term ctx) 5 :=
  index ::ᵥ fuel ::ᵥ context ::ᵥ formula ::ᵥ certificate ::ᵥ nil

/-- FOUR unbounded symbolic runtime inputs; this is not a numeral family. -/
def emptyClause (pF : Program 1) : Sentence :=
  .all (.all (.all (.all
    (.equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
      (input (.var 3) (.var 2) (.var 1) (.var 0) .zero)) .zero))))

/-- The original source checker, actual index c and three internally bound
variables fuel/formula/certificate. No external finite bound is present. -/
def nonemptyClause (pF : Program 1) (c : Code) : Sentence :=
  .all (.all (.all
    (.imp (.equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
      (input (Term.numeral (Encodable.encode c)) (.var 2) .zero (.var 1) (.var 0)))
      (Term.numeral 1)) (.neg (.equal (.var 0) .zero)))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifier
