module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWindowTargets
public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationDefinitions
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowProbeCode (code)
open NumberedWindowAddressApplication (application graph)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowScalarAlgorithm (Settings)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector

/-- Pure original AST constructors; no arithmetic syntax is imported by
this module. Exact structural coincidence with the older object control
programs is checked separately, not inferred from numerical coincidence. -/
def zeroAt (n : Nat) : Program n := .composition .zero Fin.elim0

def literal (n : Nat) : Nat → Program n
  | 0 => zeroAt n
  | k+1 => .composition .succ (fun _ : Fin 1 => literal n k)

def predOne : Program 1 := .recursion .zero (.projection (0 : Fin 2))

def decrementedStep : Program 3 :=
  .composition predOne (fun _ : Fin 1 => .projection (1 : Fin 3))

def truncatedSubtraction : Program 2 :=
  .recursion (.projection (0 : Fin 1)) decrementedStep

def reversedSubtraction : Program 2 :=
  .composition truncatedSubtraction (Fin.cons (.projection (1 : Fin 2))
    (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))

def reversedZeroTest : Program 2 :=
  .composition GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => reversedSubtraction)

def compareNumbers : Program 2 :=
  .composition GorbowPRInternalControl.conditional
    (Fin.cons truncatedSubtraction (Fin.cons reversedZeroTest (Fin.cons (zeroAt 2) Fin.elim0)))

def chooseBranch {n : Nat} (control zeroBranch otherBranch : Program n) : Program n :=
  .composition GorbowPRInternalControl.conditional
    (Fin.cons control (Fin.cons zeroBranch (Fin.cons otherBranch Fin.elim0)))

def bothOne {n : Nat} (p q : Program n) : Program n :=
  chooseBranch (GorbowVerifierNormalization.normalize p) (zeroAt n)
    (GorbowVerifierNormalization.normalize q)

/-- Literal program data only, with no all-code or arithmetic claims as
fields. These are the very same h0,a,A,p leaves of the original packet. -/
structure Leaves where
  baseTyped : Program 2
  fresh : Program 1
  applicationCode : Program 2
  applicationGuard : Program 3

def calibrated (s : Settings) (l : Leaves) : Prop :=
  (∀ t q, evaluate l.baseTyped (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
  (∀ q, evaluate l.fresh (q ::ᵥ nil) = Encodable.encode (probe s q)) ∧
  (∀ q u, evaluate l.applicationCode (q ::ᵥ u ::ᵥ nil) = Encodable.encode (application s q u)) ∧
  (∀ q u v, evaluate l.applicationGuard (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s q u v).toNat)

def typeLeaf (l : Leaves) (τ : ProbeTy) : Program 1 :=
  .composition l.baseTyped (Fin.cons (literal 1 (code τ)) (Fin.cons (Program.projection (0 : Fin 1)) Fin.elim0))

def afterPredecessor {n : Nat} (a : Program n) : Program n :=
  .composition predOne (Fin.cons a Fin.elim0)

def resultGuard (l : Leaves) (codomain : Program 1) : Program 3 :=
  bothOne l.applicationGuard (.composition codomain (Fin.cons (Program.projection (2 : Fin 3)) Fin.elim0))

def applicationPart (l : Leaves) (codomain : Program 1) : Program 2 :=
  chooseBranch l.applicationCode (zeroAt 2)
    (.composition (resultGuard l codomain)
      (Fin.cons (Program.projection (0 : Fin 2))
        (Fin.cons (Program.projection (1 : Fin 2)) (Fin.cons (afterPredecessor l.applicationCode) Fin.elim0))))

def arrowPart (l : Leaves) (codomain : Program 1) : Program 1 :=
  chooseBranch l.fresh (zeroAt 1)
    (.composition (applicationPart l codomain)
      (Fin.cons (Program.projection (0 : Fin 1)) (Fin.cons (afterPredecessor l.fresh) Fin.elim0)))

def verify (l : Leaves) : ProbeTy → Program 1
  | .ground => typeLeaf l .ground
  | .arrow σ τ => bothOne (typeLeaf l (.arrow σ τ)) (arrowPart l (verify l τ))

def typeTest (τ : ProbeTy) : Program 2 :=
  .composition compareNumbers (Fin.cons (Program.projection (0 : Fin 2)) (Fin.cons (literal 2 (code τ)) Fin.elim0))

def liftBranch (l : Leaves) (τ : ProbeTy) : Program 2 :=
  .composition (verify l τ) (Fin.cons (Program.projection (1 : Fin 2)) Fin.elim0)

def dispatch (l : Leaves) : List ProbeTy → Program 2
  | [] => zeroAt 2
  | τ :: ts => chooseBranch (typeTest τ) (dispatch l ts) (liftBranch l τ)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgram
