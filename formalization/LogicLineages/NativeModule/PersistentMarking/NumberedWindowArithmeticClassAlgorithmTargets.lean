module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticLeastClass
public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAlgorithmTargets
open Spine NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticLeastClass
open NumberedWindowPrimaryClassList NumberedWindowPrimaryCoverSyntax NumberedWindowPrimaryExchangeBits
open NumberedWindowFiniteSaturation NumberedWindowLiteralEquality

def codedExchange (S : Signature) (K Γ : List Ty) (τ : Ty) (a b : Nat) : Bool :=
  match decodeTerm a, decodeTerm b with
  | some A, some B => finiteExchangeBit S K Γ τ A B
  | _, _ => false

def ExactPrimaryRounds : Prop := ∀ S K Γ τ (vs : List NTerm) Q n,
  NumberedWindowClassAlgorithm.rounds (codedExchange S K Γ τ) (vs.map encodeTerm) (encodeTerm Q) n =
    (rounds vs termEq (finiteExchangeBit S K Γ τ) Q n).map encodeTerm

def ExactPrimaryListAndLeast : Prop := ∀ S K Γ τ Q,
  (NumberedWindowClassAlgorithm.members (codedExchange S K Γ τ) ((cover S K Q).map encodeTerm) (encodeTerm Q) =
    (finiteClassList S K Γ τ Q).map encodeTerm) ∧
  NumberedWindowClassAlgorithm.least (codedExchange S K Γ τ) ((cover S K Q).map encodeTerm) (encodeTerm Q) =
    leastCode S K Γ τ Q

end LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAlgorithmTargets
