module

public import LogicLineages.ComputabilityKnowledge.GorbowFixedGroundProgramsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms.Targets
open GorbowPRProgram GorbowPublishedDCB

/-- A FIXED typed program on variable numeric lists, with literal length rejection. -/
def SingleProgram : Prop :=
  ∀ n (p : Program n), Primrec (checkedEvaluation p)

/-- Genuine joint tag/argument effectivity of the UNCHANGED fixed finite registry.
Neither the registry nor the AST is a runtime argument of this Primrec function. -/
def FixedRegistry : Prop :=
  ∀ n (p : Program n),
    Primrec (fun x : Nat × List Nat => GorbowPRRegistry.dispatch p x.1 x.2)

/-- The entire raw-input decoded-header function, including every failure/default. -/
def DefiningDispatcher : Prop :=
  ∀ n (p : Program n), Primrec (GorbowPRDefiningEquations.functionProgram p)

/-- Both ACTUAL entire named-overlay fields, not just finitely many named headers. -/
def NamedOverlay : Prop :=
  ∀ pF pR : Program 1,
    Primrec (GorbowNamedRegistryInterpretation.functionProgram pF pR) ∧
    Primrec (GorbowNamedRegistryInterpretation.relationProgram pF pR)

/-- Fixed ordinary PR ASTs for both real published-ground fields on ALL raw inputs.
Existence from Primrec evidence is not an executable compiler from arbitrary AST data. -/
def ActualPrograms : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∃ u r : Program 1, ∀ x : Nat,
    evaluate u (x ::ᵥ List.Vector.nil) = (GorbowPublishedModel.ground pF pR q).universalFunction x ∧
    evaluate r (x ::ᵥ List.Vector.nil) =
      (if GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR x then 1 else 0)

def Target : Prop := SingleProgram ∧ FixedRegistry ∧ DefiningDispatcher ∧ NamedOverlay ∧ ActualPrograms
end LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms.Targets
