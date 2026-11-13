module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomTargets
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMP
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB List.Vector

/-- Original installed source checker, retaining an arbitrary certificate
TERM. Its formula number and fuel remain fixed external naturals. -/
def checkerAt {n : Nat} (pF : Program 1) (c : Code) (fuel formula : Nat)
    (certificate : Term n) : Formula n :=
  .equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
    (Term.numeral (Encodable.encode c) ::ᵥ Term.numeral fuel ::ᵥ Term.numeral 0 ::ᵥ
      Term.numeral formula ::ᵥ certificate ::ᵥ nil)) (Term.numeral 1)

/-- The two certificate variables are genuine OBJECT variables. The code
of rho remains in BOTH input formulas, and the conclusion is original prD. -/
def matrix (pF : Program 1) (c : Code) (sigma tau : Sentence) (s t : Nat) : Formula 2 :=
  .imp (checkerAt pF c s
    (GorbowSortedSyntaxCode.formulaCode (.imp (rho pF c) (.imp sigma tau))) (.var 1))
    (.imp (checkerAt pF c t
      (GorbowSortedSyntaxCode.formulaCode (.imp (rho pF c) sigma)) (.var 0))
      (GorbowTheoryProof.weakenClosed 2 (prD pF c tau)))

/-- The actual bounded INTERNAL MP fragment. Bounds are external fixed
naturals, fuel values are external fixed naturals, and both certificate
variables are bound inside the formula. This is not unbounded source HB2. -/
def statement (pF : Program 1) (c : Code) (sigma tau : Sentence)
    (s t boundImp boundAnte : Nat) : Sentence :=
  SourceBaseCompletion.BoundedRange.bounded boundImp
    (SourceBaseCompletion.BoundedRange.bounded boundAnte (matrix pF c sigma tau s t))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMP

namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMPTargets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Original checker preservation at every finite rectangle of certificate
values, derived in S, with no checker-correctness or HB assumption. The
unchanged full unbounded comparator remains HBAxiomTargets' original one. -/
def BoundedSourceMP : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ (sigma tau : Sentence) (s t boundImp boundAnte : Nat),
    Nonempty (Derivation (S pF pR q)
      (BoundedMP.statement pF c sigma tau s t boundImp boundAnte))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMPTargets
