module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RecombinationProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedNumericDecoding SourceProof

def andN (a b : Nat) : Nat := if a = 0 then 0 else b
/-- Literal local source Fields branch with numeric child answers. This retains
nonboolean arbitrary answer behavior required by the total native layer law. -/
def nodeValue {n : Nat} (S H : List Nat) (labels tupleBound bound : Nat) (answers : List Nat) : Code (Fin n) → Nat
  | .var index => (decide (index < bound)).toNat
  | .lam typ _ => andN (decide (typeNumber typ ∈ S)).toNat (answers[0]?.getD 0)
  | .app typ _ _ | .argumentsCons typ _ _ =>
      andN (decide (typeNumber typ ∈ S)).toNat (andN (answers[0]?.getD 0) (answers[1]?.getD 0))
  | .bottom typ => (decide (typeNumber typ ∈ S)).toNat
  | .ordinary head _ => andN (decide (headNumber head ∈ H)).toNat (answers[0]?.getD 0)
  | .numbered label head typ _ types _ =>
      andN (decide (label ≤ labels)).toNat
        (andN (decide (headNumber head ∈ H)).toNat
          (andN (decide (typeNumber typ ∈ S)).toNat
            (andN (answers[0]?.getD 0)
              (andN (decide (types.length ≤ tupleBound)).toNat
                (andN (types.all (fun t => decide (typeNumber t ∈ S))).toNat (answers[1]?.getD 0))))))
  | .argumentsNil => 1

theorem boolAnd (a b : Bool) : andN a.toNat b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

def recombination (n key param : Nat) (answers : List Nat) : Option Nat :=
  some (match decodeCode n (Nat.unpair key).1 with
    | none => 0
    | some c => nodeValue (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param)
        (Nat.unpair key).2 answers c)

theorem sourceLaw (n : Nat) (c : Code (Fin n)) (bound param : Nat) :
    nodeValue (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) bound
      ((KeyProof.sourceChildren bound c).map (fun x => value n (Nat.pair (codeNumber x.1) x.2) param)) c =
        (codeFields (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) bound c).toNat := by
  cases c <;> simp only [KeyProof.sourceChildren,List.map_cons,List.map_nil,valueImage,
    nodeValue,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,boolAnd,codeFields,Bool.and_assoc,Bool.toNat_true]

theorem recursiveLaw (n key param : Nat) :
    recombination n key param ((KeyProof.keys key).map (fun child => value n child param)) =
      some (value n key param) := by
  have hk : Nat.pair (Nat.unpair key).1 (Nat.unpair key).2 = key := Nat.pair_unpair key
  cases hc : decodeCode n (Nat.unpair key).1 with
  | none => simp only [recombination,value,hc,Option.map_none,Option.getD_none]
  | some c =>
    have he := NumberedNumericDecodingProof.codeNumericSound n (Nat.unpair key).1 c hc
    have hkey : Nat.pair (codeNumber c) (Nat.unpair key).2 = key := by rw [he]; exact hk
    have hi : KeyProof.keys key = (KeyProof.sourceChildren (Nat.unpair key).2 c).map
        (fun x => Nat.pair (codeNumber x.1) x.2) := by
      conv_lhs => rw [← hkey]
      exact KeyProof.sourceImage n c (Nat.unpair key).2
    simp only [recombination,hc,value,Option.map_some,Option.getD_some,hi,List.map_map]
    exact congrArg some (sourceLaw n c (Nat.unpair key).2 param)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RecombinationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RecombinationProof
