module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.Targets
open GorbowSyntax GorbowTheoryProof GorbowPRProgram

def UniformAxiomChecker : Prop := Primrec (fun p : Parameters × List Nat => axiomCheck p.1 p.2)

def BoundedMonotonicity : Prop := ∀ c s t, s ≤ t → ∀ sigma : Sentence,
  boundedTheory (c,s) sigma → boundedTheory (c,t) sigma

def ExactAxiomUnion : Prop := ∀ c (sigma : Sentence),
  enumeratedTheory c sigma ↔ ∃ fuel, boundedTheory (c,fuel) sigma

/-- Every actual finite derivation over the c.e. theory is already a derivation
at one finite global stage, also in open contexts and under generalization. -/
def FiniteProofStage : Prop := ∀ c n (phi : Formula n),
  Nonempty (Derivation (enumeratedTheory c) phi) ↔
    ∃ fuel, Nonempty (Derivation (boundedTheory (c,fuel)) phi)

/-- Simultaneous parameter uniformity, not a family of fixed-program claims. -/
def UniformNumericChecker : Prop :=
  Primrec (fun p : Parameters × Nat × Nat × Nat => check p.1 p.2.1 p.2.2.1 p.2.2.2)

def ExactNumericAcceptance : Prop := ∀ c n formula,
  (∃ fuel certificate, check (c,fuel) n formula certificate = true) ↔
  ∃ phi : Formula n, formula = GorbowSortedSyntaxCode.formulaCode phi ∧
    Nonempty (Derivation (enumeratedTheory c) phi)

/-- One fixed finite primitive-recursive AST works for every ordinary axiom
program, fuel, context, formula number and numeric certificate. -/
def FixedUniversalProgram : Prop := ∃ q : Program 5,
  ∀ c fuel n formula certificate,
    evaluate q (arguments c fuel n formula certificate) =
      if check (c,fuel) n formula certificate then 1 else 0

def Target : Prop := UniformAxiomChecker ∧ BoundedMonotonicity ∧ ExactAxiomUnion ∧
  FiniteProofStage ∧ UniformNumericChecker ∧ ExactNumericAcceptance ∧ FixedUniversalProgram

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.Targets
