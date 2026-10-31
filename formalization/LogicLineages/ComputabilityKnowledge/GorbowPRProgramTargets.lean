module

public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Targets
open List.Vector

def PrimitiveEvaluation : Prop :=
  ∀ n (p : Program n), Primrec (evaluate p)

def AllPrimitiveFunctions : Prop :=
  ∀ n (f : List.Vector Nat n → Nat), Primrec f →
    ∃ p : Program n, ∀ v, evaluate p v = f v

def UnaryCorrespondence : Prop :=
  ∀ f : Nat → Nat, Primrec f ↔
    ∃ p : Program 1, ∀ x, evaluate p (x ::ᵥ List.Vector.nil) = f x

def RecursionZero : Prop :=
  ∀ n (f : Program n) (g : Program (n + 2)) (v : List.Vector Nat n),
    evaluate (.recursion f g) (0 ::ᵥ v) = evaluate f v

def RecursionSuccessor : Prop :=
  ∀ n (f : Program n) (g : Program (n + 2)) (v : List.Vector Nat n) (k : Nat),
    evaluate (.recursion f g) (Nat.succ k ::ᵥ v) =
      evaluate g (k ::ᵥ evaluate (.recursion f g) (k ::ᵥ v) ::ᵥ v)

end LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Targets
