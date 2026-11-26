module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedNormalizationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildInheritanceCounterexampleDefinitions
open UniformCertificateCompletion
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport (constant)

/- INVESTIGATIVE NATIVE FIXTURE ONLY. No fact below is asserted proved.
The literal old selected tuple is used; no evaluator or new rank guard is installed.
The unrelated source/computability fields of p are preserved and unused by this key. -/
def tau : Nat := 0
def arrow : Nat := 1 + Nat.pair tau tau
def rawVar : Nat := Nat.pair 0 0
def rawBottom : Nat := Nat.pair 3 tau
def rawU : Nat := Nat.pair 1 (Nat.pair tau rawVar)
def rawV : Nat := Nat.pair 1 (Nat.pair tau rawBottom)
def rawNil : Nat := Nat.pair 6 0
def args (raw : Nat) : Nat := Nat.pair 7 (Nat.pair arrow (Nat.pair raw rawNil))
def ordinary (head raw : Nat) : Nat := Nat.pair 4 (Nat.pair head (args raw))
def fu : Nat := Nat.pair arrow (ordinary 0 rawU)
def fv : Nat := Nat.pair arrow (ordinary 0 rawV)
def au : Nat := Nat.pair tau (ordinary 1 rawU)
def av : Nat := Nat.pair tau (ordinary 1 rawV)
def application (fn arg : Nat) : Nat :=
  Nat.pair tau (Nat.pair 2 (Nat.pair tau (Nat.pair fn arg)))
def parentLeft : Nat := application (ordinary 0 rawU) (ordinary 1 rawV)
def parentRight : Nat := application (ordinary 0 rawV) (ordinary 1 rawU)
def parentCommon : Nat := application (ordinary 0 rawU) (ordinary 1 rawU)
def parameter : Nat := Nat.pair 0 0

def rawUProgram (n : Nat) : Program n :=
  pairOf (constant n 1) (pairOf (constant n 0) (pairOf (constant n 0) (constant n 0)))
def argsProgram (n : Nat) : Program n :=
  pairOf (constant n 7) (pairOf (constant n 1)
    (pairOf (rawUProgram n) (pairOf (constant n 6) (constant n 0))))
def ordinaryProgram (n head : Nat) : Program n :=
  pairOf (constant n 4) (pairOf (constant n head) (argsProgram n))
def representative : Program 2 :=
  InternalAcceptance.branch (leftOf (.projection 0))
    (pairOf (constant 2 0) (ordinaryProgram 2 1))
    (pairOf (constant 2 1) (ordinaryProgram 2 0))
def H : Program 1 :=
  InternalAcceptance.branch (.projection 0)
    (consOf (constant 1 1) (consOf (constant 1 1) (constant 1 0)))
    (consOf (constant 1 0) (consOf (constant 1 1) (constant 1 0)))
def G : Program 1 := constant 1 1
def W : Program 2 := constant 2 1
def P : Program 3 := constant 3 1
def fixture (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := { p.base with oldRepresentative := representative, member := constant 2 1 },
    window := constant 1 1 }
def s (p : GlobalSourcePackage.Inputs) :=
  ObservedNormalizationTargets.preminimum (fixture p) H G W
def key (p : GlobalSourcePackage.Inputs) : Program 2 :=
  SixSol20261113.Erasure.ObservedPut.key (fixture p) H G W
def domain (p : GlobalSourcePackage.Inputs) : Program 2 :=
  OriginalActiveClassKernel.domainProgram (s p) H G W
def relation (p : GlobalSourcePackage.Inputs) : Program 3 :=
  OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
    (OriginalActiveObservedClass.classTest (s p) H G W OriginalRawSyntaxTransport.variableRankPackedRaw
      (OriginalClassContextAllPositionSelection.classTest (s p) H G W P))
def eval2 (F : Program 2) (x y : Nat) : Nat := evaluate F (List.Vector.ofFn ![x,y])
def eval3 (F : Program 3) (x y z : Nat) : Nat := evaluate F (List.Vector.ofFn ![x,y,z])

/-- Desired complete diagnostic witness, NOT a checked theorem. This records
all actual relational guards rather than assuming a black-box key collapse.
Both pairs of corresponding children have matching source types by construction. -/
def Candidate (p : GlobalSourcePackage.Inputs) : Prop :=
  eval2 (domain p) parentLeft parameter = 1 ∧
  eval2 (domain p) parentRight parameter = 1 ∧
  eval2 (domain p) fu parameter = 1 ∧ eval2 (domain p) fv parameter = 1 ∧
  eval2 (domain p) au parameter = 1 ∧ eval2 (domain p) av parameter = 1 ∧
  eval2 (key p) fu parameter = fu ∧ eval2 (key p) fv parameter = fu ∧
  eval2 (key p) au parameter = au ∧ eval2 (key p) av parameter = au ∧
  eval2 (key p) parentLeft parameter = parentCommon ∧
  eval2 (key p) parentRight parameter = parentCommon ∧
  eval3 (relation p) parentLeft parentRight parameter = 1 ∧
  eval3 (relation p) fu fv parameter = 0 ∧
  eval3 (relation p) av au parameter = 0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildInheritanceCounterexampleDefinitions
