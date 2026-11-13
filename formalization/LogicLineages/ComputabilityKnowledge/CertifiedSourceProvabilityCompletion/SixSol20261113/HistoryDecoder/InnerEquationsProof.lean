module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepInvariantProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph StepNormalProof

def innerStepTag (tag : Nat) := tag + stepTag (.projection (2 : Fin 3))
def innerPairTag (right : Bool) (tag : Nat) := stepPairTag right (innerStepTag tag)
def innerCall {ctx : Nat} (tag : Nat) (count a code seed : Term ctx) : Term ctx :=
  call tag (count ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)
def pairValue {ctx : Nat} (right : Bool) (tag : Nat) (u v : Term ctx) : Term ctx :=
  call (innerPairTag right tag) (u ::ᵥ v ::ᵥ nil)

theorem substInner {m n : Nat} (sub : Fin m → Term n) tag (count a code seed : Term m) :
    substitute sub (innerCall tag count a code seed) =
      innerCall tag (substitute sub count) (substitute sub a) (substitute sub code) (substitute sub seed) := by
  simp only [innerCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substPair {m n : Nat} (sub : Fin m → Term n) right tag (u v : Term m) :
    substitute sub (pairValue right tag u v) = pairValue right tag (substitute sub u) (substitute sub v) := by
  simp only [pairValue,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substChosen {m n : Nat} (sub : Fin m → Term n) right (u v : Term m) :
    substitute sub (chosen right u v) = chosen right (substitute sub u) (substitute sub v) := by
  cases right <;> rfl

theorem stepInstalled {n : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) :
    (nodes p)[innerStepTag tag]? = some ⟨5,innerStep right⟩ :=
  SixSol20261112.Fuel.Equations.recursionStepChild p tag (.projection (2 : Fin 3)) (innerStep right) ht

theorem innerZero {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) (a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (innerCall tag .zero a code seed) seed)) := by
  have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨4,inner right⟩ 1
    ⟨3,.projection (2 : Fin 3)⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 3 (.projection (2 : Fin 3)) (innerStep right))
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation
    n p tag 3 (.projection (2 : Fin 3)) (innerStep right) ht ctx (a ::ᵥ code ::ᵥ seed ::ᵥ nil)
  obtain ⟨hp⟩ := SixSol20261112.Fuel.Equations.projection p (tag+1) (2 : Fin 3) hb (a ::ᵥ code ::ᵥ seed ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hz hp⟩

theorem innerSuccessor {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) (count a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (innerCall tag (.succ count) a code seed)
        (call (innerStepTag tag) (count ::ᵥ innerCall tag count a code seed ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)))) :=
  GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation
    n p tag 3 (.projection (2 : Fin 3)) (innerStep right) ht ctx count (a ::ᵥ code ::ᵥ seed ::ᵥ nil)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerEquationsProof
