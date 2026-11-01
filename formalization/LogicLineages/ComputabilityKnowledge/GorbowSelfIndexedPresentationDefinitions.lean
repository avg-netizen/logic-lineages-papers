module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCode
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section
/-! An actual finite syntactically self-indexed axiom presentation. The unary
formula template is instantiated at the ordinary program's OWN code numeral;
no self-index/representability field is added to a theory structure. The
source DCB reflection template and its semantic arithmetic calibration remain
separate consumers of this general literal-syntax construction. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation
open GorbowSyntax
abbrev Code := Nat.Partrec.Code

def instanceRaw (template : Formula 1) (c : Code) : Option (List Nat) :=
  GorbowInstanceCode.instanceCode 0 (GorbowFormulaPrefixCode.encode template)
    (GorbowCodeConstructors.numeral (Encodable.encode c))

def axiomCodes (base : List Sentence) (template : Formula 1) (c : Code) : List (List Nat) :=
  base.map GorbowFormulaPrefixCode.encode ++ [(instanceRaw template c).getD []]

def check (base : List Sentence) (template : Formula 1) (c : Code) (raw : List Nat) : Bool :=
  decide (raw ∈ axiomCodes base template c)

def numericCheck (base : List Sentence) (template : Formula 1) (c : Code) (input : Nat) : Nat :=
  match Encodable.decode (α := List Nat) input with
  | none => 0
  | some raw => if check base template c raw then 1 else 0

def axioms (base : List Sentence) (template : Formula 1) (c : Code) : List Sentence :=
  base ++ [GorbowStandardInstances.instantiate template (Term.numeral (Encodable.encode c))]

def Theory (base : List Sentence) (template : Formula 1) (c : Code) : Sentence → Prop :=
  fun sigma => sigma ∈ axioms base template c

end LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation
