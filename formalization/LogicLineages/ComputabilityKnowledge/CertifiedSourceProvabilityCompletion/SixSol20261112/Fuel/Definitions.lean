module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowFormulaSubstitution List.Vector

def zeroProgram (n : Nat) : Program n := .composition .zero Fin.elim0
def oneProgram (n : Nat) : Program n := .composition .succ (fun _ => zeroProgram n)

/-- Both normalizers are literal ASTs; no Boolean codomain of opaque q0 is
assumed on arbitrary raw runtime inputs. -/
def isZero : Program 1 := .recursion (oneProgram 0) (zeroProgram 2)
def isOne : Program 1 :=
  .recursion .zero (.composition isZero (fun _ => .projection (0 : Fin 2)))

/-- Left short circuit: or(0,x)=x; or(k+1,x)=k+1. At Boolean inputs this is
OR, and the literal source equation or(1,x)=1 is independent of x. -/
def leftOr : Program 2 :=
  .recursion (.projection (0 : Fin 1))
    (.composition .succ (fun _ => .projection (0 : Fin 3)))

/-- Base retained context is [index,context,formula,certificate]. -/
def baseArguments : Fin 5 → Program 4 :=
  Fin.cases (.projection (0 : Fin 4))
    (Fin.cases (zeroProgram 4)
      (Fin.cases (.projection (1 : Fin 4))
        (Fin.cases (.projection (2 : Fin 4))
          (Fin.cases (.projection (3 : Fin 4)) Fin.elim0))))

def base (q0 : Program 5) : Program 4 :=
  .composition isOne (fun _ => .composition q0 baseArguments)

/-- Recursion step context is [counter,previous,index,context,formula,cert]. -/
def nextArguments : Fin 5 → Program 6 :=
  Fin.cases (.projection (2 : Fin 6))
    (Fin.cases (.composition .succ (fun _ => .projection (0 : Fin 6)))
      (Fin.cases (.projection (3 : Fin 6))
        (Fin.cases (.projection (4 : Fin 6))
          (Fin.cases (.projection (5 : Fin 6)) Fin.elim0))))

def nextValue (q0 : Program 5) : Program 6 :=
  .composition isOne (fun _ => .composition q0 nextArguments)

def stepArguments (q0 : Program 5) : Fin 2 → Program 6 :=
  Fin.cases (.projection (1 : Fin 6)) (fun _ => nextValue q0)

def step (q0 : Program 5) : Program 6 := .composition leftOr (stepArguments q0)
def accumulator (q0 : Program 5) : Program 5 := .recursion (base q0) (step q0)

/-- Return to the ORIGINAL checker order [index,fuel,context,formula,cert]. -/
def outerArguments : Fin 5 → Program 5 :=
  Fin.cases (.projection (1 : Fin 5))
    (Fin.cases (.projection (0 : Fin 5))
      (Fin.cases (.projection (2 : Fin 5))
        (Fin.cases (.projection (3 : Fin 5))
          (Fin.cases (.projection (4 : Fin 5)) Fin.elim0))))

def verifier (q0 : Program 5) : Program 5 := .composition (accumulator q0) outerArguments

def inputs {alpha : Type} (index fuel context formula certificate : alpha) : List.Vector alpha 5 :=
  index ::ᵥ fuel ::ᵥ context ::ᵥ formula ::ᵥ certificate ::ᵥ nil

def success {ctx : Nat} (tag : Nat) (index fuel context formula cert : Term ctx) : Formula ctx :=
  .equal (GorbowPRDefiningEquations.call tag (inputs index fuel context formula cert)) (Term.numeral 1)

def liftTerm {ctx : Nat} (t : Term ctx) : Term (ctx+1) := renameTerm Fin.succ t

/-- The induction variable is the increment; all original parameters remain. -/
def incrementTemplate {ctx : Nat} (tag : Nat)
    (index fuel context formula cert : Term ctx) : Formula (ctx+1) :=
  .imp (success tag (liftTerm index) (liftTerm fuel) (liftTerm context) (liftTerm formula) (liftTerm cert))
    (success tag (liftTerm index) (.add (liftTerm fuel) (.var 0))
      (liftTerm context) (liftTerm formula) (liftTerm cert))

/-- Ordinary arithmetic order, retaining both endpoints before the witness. -/
def orderGuard {ctx : Nat} (s t : Term ctx) : Formula ctx :=
  .ex (.equal (.add (liftTerm s) (.var 0)) (liftTerm t))

def stepClause (pF : Program 1) : Sentence :=
  GorbowStandardInduction.universalClosure (.imp
    (success (GorbowNamedInternalProvability.checkerTag pF)
      (.var 4 : Term 5) (.var 0) (.var 3) (.var 2) (.var 1))
    (success (GorbowNamedInternalProvability.checkerTag pF)
      (.var 4 : Term 5) (.succ (.var 0)) (.var 3) (.var 2) (.var 1)))

def incrementClause (pF : Program 1) : Sentence :=
  GorbowStandardInduction.universalClosure
    (incrementTemplate (GorbowNamedInternalProvability.checkerTag pF)
      (.var 4 : Term 5) (.var 0) (.var 3) (.var 2) (.var 1))

/-- Six genuinely internally quantified inputs, including both fuel values. -/
def monotonicityClause (pF : Program 1) : Sentence :=
  GorbowStandardInduction.universalClosure (.imp
    (orderGuard (.var 1 : Term 6) (.var 0))
    (.imp (success (GorbowNamedInternalProvability.checkerTag pF)
      (.var 5 : Term 6) (.var 1) (.var 4) (.var 3) (.var 2))
      (success (GorbowNamedInternalProvability.checkerTag pF)
        (.var 5 : Term 6) (.var 0) (.var 4) (.var 3) (.var 2))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel
