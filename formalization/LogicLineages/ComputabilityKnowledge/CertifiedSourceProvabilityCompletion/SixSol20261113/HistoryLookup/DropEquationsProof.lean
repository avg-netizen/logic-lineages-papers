module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DestructorProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DropEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

def tailTag (tag : Nat) := tag + stepTag (.projection (0 : Fin 1)) + 1

def dropCall {ctx : Nat} (tag : Nat) (index code : Term ctx) : Term ctx := call tag (index ::ᵥ code ::ᵥ nil)

theorem substDrop {m n : Nat} (sub : Fin m → Term n) tag (index code : Term m) :
    substitute sub (dropCall tag index code) = dropCall tag (substitute sub index) (substitute sub code) := by
  simp only [dropCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substCons {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substitute sub (consCall tag a b) = consCall tag (substitute sub a) (substitute sub b) := by
  simp only [consCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem tailInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,drop⟩) :
    (nodes p)[tailTag tag]? = some ⟨1,tail⟩ := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag (.projection (0 : Fin 1)) dropStep ht
  exact SixSol20261112.Fuel.Equations.functionChild p _ tail (fun _ => .projection (1 : Fin 3)) hs

theorem dropZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,drop⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (dropCall tag .zero code) code)) := by
  have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,drop⟩ 1 ⟨1,.projection (0 : Fin 1)⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 1 (.projection (0 : Fin 1)) dropStep)
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 (.projection (0 : Fin 1)) dropStep ht ctx (code ::ᵥ nil)
  obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+1) (0 : Fin 1) hb (code ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hz hp⟩

theorem dropSuccessor {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,drop⟩) (index code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (dropCall tag (.succ index) code) (call (tailTag tag) (dropCall tag index code ::ᵥ nil)))) := by
  let st := tag + stepTag (.projection (0 : Fin 1))
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag (.projection (0 : Fin 1)) dropStep ht
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1 (.projection (0 : Fin 1)) dropStep ht ctx index (code ::ᵥ nil)
  have hv : ∀ i : Fin 1, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (st+argumentTag tail (fun _ : Fin 1 => .projection (1 : Fin 3)) i)
        (index ::ᵥ dropCall tag index code ::ᵥ code ::ᵥ nil)) ((dropCall tag index code ::ᵥ nil).get i))) := by
    intro i
    cases i using Fin.cases with
    | zero =>
        have hp := SixSol20261112.Fuel.Equations.argumentChild p st tail (fun _ : Fin 1 => .projection (1 : Fin 3)) hs 0
        exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 3) hp _
    | succ i => exact Fin.elim0 i
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p st tail (fun _ : Fin 1 => .projection (1 : Fin 3)) hs
    (index ::ᵥ dropCall tag index code ::ᵥ code ::ᵥ nil) (dropCall tag index code ::ᵥ nil) hv
  exact ⟨Logic.trans _ _ _ hr hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DropEquationsProof
