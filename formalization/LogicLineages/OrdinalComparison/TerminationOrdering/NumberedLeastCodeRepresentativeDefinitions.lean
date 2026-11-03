module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassProof
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Finset.Max
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentative
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedFinitePrimaryClass

def typeNumber : Ty → Nat
  | .ground => 0
  | .arrow sigma tau => 1+Nat.pair (typeNumber sigma) (typeNumber tau)

def typesNumber : List Ty → Nat
  | [] => 0
  | tau::rest => 1+Nat.pair (typeNumber tau) (typesNumber rest)

def headNumber {n : Nat} : HeadCode (Fin n) → Nat
  | .zero => Nat.pair 0 0
  | .succ => Nat.pair 1 0
  | .cases tau => Nat.pair 2 (typeNumber tau)
  | .recursor tau => Nat.pair 3 (typeNumber tau)
  | .application sigma tau => Nat.pair 4 (Nat.pair (typeNumber sigma) (typeNumber tau))
  | .ranked s => Nat.pair 5 s.val

def codeNumber {n : Nat} : Code (Fin n) → Nat
  | .var i => Nat.pair 0 i
  | .lam sigma body => Nat.pair 1 (Nat.pair (typeNumber sigma) (codeNumber body))
  | .app sigma q a => Nat.pair 2 (Nat.pair (typeNumber sigma) (Nat.pair (codeNumber q) (codeNumber a)))
  | .bottom tau => Nat.pair 3 (typeNumber tau)
  | .ordinary head base => Nat.pair 4 (Nat.pair (headNumber head) (codeNumber base))
  | .numbered k head tau base types extras => Nat.pair 5
      (Nat.pair k (Nat.pair (headNumber head) (Nat.pair (typeNumber tau)
        (Nat.pair (codeNumber base) (Nat.pair (typesNumber types) (codeNumber extras))))))
  | .argumentsNil => Nat.pair 6 0
  | .argumentsCons tau q rest => Nat.pair 7 (Nat.pair (typeNumber tau) (Nat.pair (codeNumber q) (codeNumber rest)))

def packedNumber {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) : Nat :=
  Nat.pair (typeNumber q.1) (codeNumber (termCode q.2))

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} : DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

def classNumbers {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma) : Finset Nat :=
  (primaryClass symbols S q).image packedNumber

theorem classNumbersNonempty {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma) : (classNumbers symbols S q).Nonempty := by
  exact ⟨packedNumber q,Finset.mem_image.mpr ⟨q,NumberedFinitePrimaryClassProof.initialMember symbols S q _,rfl⟩⟩

def representativeCode {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma) : Nat :=
  (classNumbers symbols S q).min' (classNumbersNonempty symbols S q)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentative
