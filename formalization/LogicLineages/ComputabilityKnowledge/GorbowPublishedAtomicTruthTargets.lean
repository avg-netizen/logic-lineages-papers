module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruthDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowPublishedModel GorbowStandardInstances GorbowSortedSyntaxCode GorbowRegistryTuple
open GorbowAtomicTruth

/-- The actual arithmetic-evaluation and simultaneous-substitution source headers.
This is not an equality of entire legacy and published-ground UF interpretations. -/
def HeaderCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    (∀ (t : Term 0), ArithmeticTerm t → ∀ I,
      (ground pF pR q).universalFunction (header 1 1 [termCode t]) =
        t.realize I Fin.elim0) ∧
    (∀ m (R : Formula m) (sigma : Fin m → Term 0),
      (ground pF pR q).universalFunction
        (header 3 1 [m,formulaCode R,tuple (List.ofFn (fun i => termCode (sigma i)))]) =
        formulaCode (GorbowFormulaSubstitution.substituteFormula sigma R))

/-- Exact actual source code of a simultaneous arithmetic-term atomic instance,
for arbitrary injectively listed free names and their original ambient context. -/
def CodeCalibration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ n m (R : Formula m) (names : Fin n → Fin m), Function.Injective names →
  ∀ (ts : Fin n → Term 0), (∀ j, ArithmeticTerm (ts j)) →
  ∀ (P : Nat → Prop) env, (∀ j, env j = termCode (ts j)) →
    (instanceCodeTerm R names).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (GorbowFormulaSubstitution.substituteFormula
        (GorbowNameDictionary.dictionary names ts) R)

/-- EVERY source L-minus atomic FS schema, universally coded over arithmetic
instance parameters, true at EVERY actual positive revision stage. The atom may
contain the actual fixed universal relation/function; no legacy-ground identity. -/
def PositiveAtomicSchemas : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ n m (R : Formula m) (names : Fin n → Fin m),
    GorbowRevisionComposition.AtomicMinus R → Function.Injective names →
    GorbowNameDictionary.Covers R names → ∀ k : Nat,
    (atomicAxiom R names).realize
      (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0

def Target : Prop := HeaderCalibration ∧ CodeCalibration ∧ PositiveAtomicSchemas
end LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth.Targets
