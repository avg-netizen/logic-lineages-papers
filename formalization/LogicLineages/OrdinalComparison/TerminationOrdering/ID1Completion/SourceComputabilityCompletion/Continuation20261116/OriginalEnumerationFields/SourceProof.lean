module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.KeyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ListNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SourceProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedLeastCodeRepresentativeSupportProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedNumericDecoding
open Continuation20261115
/-- Independent source-syntax recursion with raw finite admissibility lists.
Only the bound changes under a lambda. No enumeration/depth definition occurs. -/
def codeFields {n : Nat} (S H : List Nat) (labels tupleBound : Nat) : Nat → Code (Fin n) → Bool
  | bound,.var index => decide (index < bound)
  | bound,.lam typ child => decide (typeNumber typ ∈ S) && codeFields S H labels tupleBound (bound+1) child
  | bound,.app typ left right => decide (typeNumber typ ∈ S) && codeFields S H labels tupleBound bound left && codeFields S H labels tupleBound bound right
  | _,.bottom typ => decide (typeNumber typ ∈ S)
  | bound,.ordinary head child => decide (headNumber head ∈ H) && codeFields S H labels tupleBound bound child
  | bound,.numbered label head typ base types extra =>
      decide (label ≤ labels) && decide (headNumber head ∈ H) && decide (typeNumber typ ∈ S) &&
        codeFields S H labels tupleBound bound base && decide (types.length ≤ tupleBound) &&
        types.all (fun t => decide (typeNumber t ∈ S)) && codeFields S H labels tupleBound bound extra
  | _,.argumentsNil => true
  | bound,.argumentsCons typ left right => decide (typeNumber typ ∈ S) && codeFields S H labels tupleBound bound left && codeFields S H labels tupleBound bound right

theorem typeMember (S : List Source.Ty) (ty : Source.Ty) : typeNumber ty ∈ S.map typeNumber ↔ ty ∈ S := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := List.mem_map.mp h
    have e := typeNumberInjective he
    subst x
    exact hx
  · intro h
    exact List.mem_map.mpr ⟨ty,h,rfl⟩

theorem headMember {n : Nat} (H : List (HeadCode (Fin n))) (head : HeadCode (Fin n)) :
    headNumber head ∈ H.map headNumber ↔ head ∈ H := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := List.mem_map.mp h
    have e := headNumberInjective he
    subst x
    exact hx
  · intro h
    exact List.mem_map.mpr ⟨head,h,rfl⟩

theorem originalFields {n : Nat} (S : List Source.Ty) (H : List (HeadCode (Fin n)))
    (labels tupleBound bound : Nat) (c : Code (Fin n)) :
    codeFields (S.map typeNumber) (H.map headNumber) labels tupleBound bound c = true ↔
      NumberedAuxiliaryEnumeration.Fields S H labels tupleBound bound c := by
  induction c generalizing bound <;>
    simp_all [codeFields,NumberedAuxiliaryEnumeration.Fields,typeMember,headMember,and_assoc]

def rawTypes (param : Nat) : List Nat := (decodeNumbers (Nat.unpair param).1).getD []
def rawHeads (n param : Nat) : List Nat :=
  ((decodeNumbers (Nat.unpair (Nat.unpair param).2).1).getD []).map (fun h =>
    ((Encodable.decode (α := HeadCode (Fin n)) h).map headNumber).getD 0)
def rawLabels (param : Nat) : Nat := (Nat.unpair (Nat.unpair (Nat.unpair param).2).2).1
def rawTupleBound (param : Nat) : Nat := (Nat.unpair (Nat.unpair (Nat.unpair param).2).2).2
/-- All-raw totalization of the independent source recursion: decoder failure0. -/
def value (n key param : Nat) : Nat :=
  ((decodeCode n (Nat.unpair key).1).map (fun c =>
    (codeFields (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param)
      (Nat.unpair key).2 c).toNat)).getD 0

theorem valueImage (n : Nat) (c : Code (Fin n)) (bound param : Nat) :
    value n (Nat.pair (codeNumber c) bound) param =
      (codeFields (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) bound c).toNat := by
  simp only [value,Nat.unpair_pair,NumberedNumericDecodingProof.codeRoundTrip,Option.map_some,Option.getD_some]

theorem valueBoolean (n key param : Nat) : value n key param = 0 ∨ value n key param = 1 := by
  unfold value
  cases hc : decodeCode n (Nat.unpair key).1 with
  | none => simp
  | some c =>
    simp only [Option.map_some,Option.getD_some]
    cases codeFields (rawTypes param) (rawHeads n param) (rawLabels param) (rawTupleBound param) (Nat.unpair key).2 c <;> simp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SourceProof
