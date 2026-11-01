module

public import LogicLineages.ComputabilityKnowledge.GorbowInternalProvabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowSelectedDistributionDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationDefinitions

@[expose] public section
/-! Collision-free insertion of an actual finite checker program into the
calibrated named syntax registry. The unused second branch preserves the
source dispatcher while retaining a literal subtree for the extra program.
This is a bridge to a concrete named arithmetic base, not a self-indexed DCB
presentation or an internal Hilbert--Bernays assumption. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector

def zeroUnary : Program 1 := .composition .zero Fin.elim0

def wrapper {n : Nat} (q : Program n) : Program 1 :=
  .composition q (fun _ => zeroUnary)

def augment {n : Nat} (p : Program 1) (q : Program n) : Program 1 :=
  .composition (.projection (0 : Fin 2)) (Fin.cases p (fun _ => wrapper q))

/-- Six padding entries, the augment root and its projection, the old p
subtree, and the wrapper root occur before q. -/
def checkerTag (p : Program 1) : Nat := 9 + (nodes p).length

def body (tag : Nat) : Formula 2 :=
  .equal (GorbowPRDefiningEquations.call tag (.var 1 ::ᵥ .var 0 ::ᵥ List.Vector.nil))
    (Term.numeral 1)

def provabilityFormula (tag : Nat) : Formula 1 := .ex (body tag)

def atCode (tag formula : Nat) : Sentence :=
  .ex (.equal (GorbowPRDefiningEquations.call tag
    (Term.numeral formula ::ᵥ .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1))

end LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability
