module

public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInduction
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
/-! Actual universally quantified primitive-recursive defining equations in
the unchanged Gorbow U/u language, for a finite dependency-closed registry.
This is not the source Base: selecting and integrating the actual syntax and
proof-checking programs, numerical derivations, arithmetic provability and
Hilbert--Bernays/Lob remain separate obligations. No ground-diagram axioms
or semantic truth assumptions are installed as proof constructors. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags List.Vector

def call {ctx arity : Nat} (tag : Nat) (args : List.Vector (Term ctx) arity) : Term ctx :=
  .universalFunction (GorbowRegistryTuple.headerTerm arity tag args.toList)

def argumentVariables (n : Nat) : List.Vector (Term n) n := List.Vector.ofFn Term.var

def tailVariables (n : Nat) : List.Vector (Term (n+1)) n :=
  List.Vector.ofFn fun i => Term.var i.succ

def equation {n : Nat} (lhs rhs : Term n) : Sentence :=
  GorbowStandardInduction.universalClosure (.equal lhs rhs)

def nodeEquations : {n : Nat} → Program n → Nat → List Sentence
  | _, .zero, tag => [equation (n:=0) (call tag List.Vector.nil) .zero]
  | _, .succ, tag => [equation (call tag (argumentVariables 1)) (.succ (.var 0))]
  | n, .projection i, tag => [equation (call tag (argumentVariables n)) (.var i)]
  | m, .composition f g, tag =>
      [equation (call tag (argumentVariables m))
        (call (tag+1) (List.Vector.ofFn fun i => call (tag + argumentTag f g i) (argumentVariables m)))]
  | _, .recursion (n:=n) f g, tag =>
      [equation (call tag (.zero ::ᵥ argumentVariables n)) (call (tag+1) (argumentVariables n)),
       equation (call tag (.succ (.var 0) ::ᵥ tailVariables n))
        (call (tag + stepTag f)
          (.var 0 ::ᵥ call tag (.var 0 ::ᵥ tailVariables n) ::ᵥ tailVariables n))]

def axioms {n : Nat} (p : Program n) : List Sentence :=
  ((nodes p).zipIdx).flatMap fun entry => nodeEquations entry.1.2 entry.2

def functionProgram {n : Nat} (p : Program n) (code : Nat) : Nat :=
  match GorbowRegistryDecoder.decodeHeader code with
  | none => 0
  | some (arity,tag,args) =>
      if arity = args.length then (dispatch p tag args).getD 0 else 0

def interpretation {n : Nat} (p : Program n) (I : Interpretation) : Interpretation :=
  { I with universalFunction := functionProgram p }

def check {n : Nat} (p : Program n) (raw : List Nat) : Bool :=
  decide (raw ∈ (axioms p).map GorbowFormulaPrefixCode.encode)

end LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations
