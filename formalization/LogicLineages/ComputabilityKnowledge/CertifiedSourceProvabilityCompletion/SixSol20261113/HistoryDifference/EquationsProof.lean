module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
open GorbowPRChildTags GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec

private def dbase : Program 1 := .projection 0
private def dstep : Program 3 := .composition predecessor (fun _ => .projection (1 : Fin 3))

def predecessorTag (tag : Nat) : Nat := tag + stepTag (Program.projection (0 : Fin 1)) + 1

theorem predecessorZero : Targets.PredecessorZero := by
  intro n p tag ht ctx
  have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨1,predecessor⟩ 1 ⟨0,Program.zero⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 0 Program.zero (.projection (0 : Fin 2)))
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 0 Program.zero
    (.projection (0 : Fin 2)) ht ctx nil
  obtain ⟨hz⟩ := Support.intoRegistry p Program.zero (tag+1) hb _
    (NamedArithmeticGraph.Equations.zero (tag+1) ctx)
  exact ⟨Logic.trans _ _ _ hr hz⟩

theorem predecessorSuccessor : Targets.PredecessorSuccessor := by
  intro n p tag ht ctx a
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag Program.zero
    (.projection (0 : Fin 2)) ht
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 0 Program.zero
    (.projection (0 : Fin 2)) ht ctx a nil
  obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+stepTag Program.zero)
    (0 : Fin 2) hs (a ::ᵥ call tag (a ::ᵥ nil) ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hr hp⟩

theorem predecessorInstalled {n : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,difference⟩) :
    (nodes p)[predecessorTag tag]? = some ⟨1,predecessor⟩ := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag dbase dstep ht
  exact SixSol20261112.Fuel.Equations.functionChild p (tag+stepTag dbase) predecessor
    (fun _ : Fin 1 => .projection (1 : Fin 3)) hs

theorem differenceZero {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,difference⟩) (b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (differenceCall tag .zero b) b)) := by
  have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,difference⟩ 1 ⟨1,dbase⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 1 dbase dstep)
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 dbase dstep ht ctx (b ::ᵥ nil)
  obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+1) (0 : Fin 1) hb (b ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hr hp⟩

theorem differenceSuccessor {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,difference⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (differenceCall tag (.succ a) b)
        (call (predecessorTag tag) (differenceCall tag a b ::ᵥ nil)))) := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag dbase dstep ht
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1 dbase dstep ht ctx a (b ::ᵥ nil)
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionProjections p (tag+stepTag dbase)
    predecessor (fun _ : Fin 1 => .projection (1 : Fin 3)) hs
    (fun _ => (1 : Fin 3)) (fun _ => rfl)
    (a ::ᵥ differenceCall tag a b ::ᵥ b ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hr hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.EquationsProof
