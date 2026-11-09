module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def constant {n : Nat} (value : Nat) : Program n :=
  match value with
  | 0 => .composition .zero Fin.elim0
  | k + 1 => .composition .succ (fun _ : Fin 1 => constant k)

/-- Exact raw packed bottom: BOTH type occurrences are the supplied code.
A malformed bottom node with mismatching outer/inner type is excluded. -/
def bottomCode : Program 1 :=
  pairOf (.projection 0) (pairOf (constant 3) (.projection 0))

def bottomTest : Program 1 :=
  InternalApplicationStepPeel.same (.projection 0)
    (.composition bottomCode (fun _ : Fin 1 => leftOf (.projection 0)))

def bottomValue (value : Nat) : Nat :=
  if value = Nat.pair (Nat.unpair value).1 (Nat.pair 3 (Nat.unpair value).1) then 1 else 0

def windowAt (window : Program 1) : Program 2 :=
  .composition window (fun _ : Fin 1 => leftOf (.projection 1))

/-- Use the validator of the EVENTUAL once-member-normalized tuple. Its AST
does not depend on oldRepresentative, so changing that leaf leaves V intact. -/
def active (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.conjunction (windowAt window)
    (InternalOriginalUniformDescentSelection.validity
      (InternalOriginalUniformContextMembership.normalizeData data))

def sameBottom (representative : Program 2) : Program 2 :=
  InternalApplicationStepPeel.same
    (.composition bottomTest (fun _ : Fin 1 => representative))
    (.composition bottomTest (fun _ : Fin 1 => .projection 0))

/-- Reject only a candidate whose EXACT bottom indicator differs. The
inactive original output, including invalid source/context cases, is retained. -/
def representative (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (active data window) data.oldRepresentative
    (InternalAcceptance.branch (sameBottom data.oldRepresentative) (.projection 0) data.oldRepresentative)

/-- Leave membership unnormalized here. L1's eventual normalizeData then
has definitionally the SAME V used by the guard above. -/
def baseData (data : Data) (window : Program 1) : Data :=
  { data with oldRepresentative := representative data window }

def readyData (data : Data) (window : Program 1) : Data :=
  InternalOriginalUniformContextMembership.normalizeData (baseData data window)

def activeGraph {α : Type} (data : Data) (window : Program 1)
    (value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (active data window) InternalOriginalStepGuard.one value parameter

def representativeGraph {α : Type} (data : Data) (window : Program 1)
    (out value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (representative data window) out value parameter

def bottomGraph {α : Type} (out value : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 bottomTest out value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentative
