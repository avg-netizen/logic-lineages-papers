module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawWitnessBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPathWitnessBits
open Spine NumberedWindowSyntax NumberedWindowLiteralEquality
open NumberedWindowRawWitnessBits
open NumberedWindowTypingBits (finiteWindowBit)

/-- One actual target term with its genuine raw-step witness.
The source is the real previous vertex, not an auxiliary guess. -/
structure RawHop where
  target : NTerm
  witness : RawWitness

/-- An empty path requires literal endpoint identity plus admission.
Every nonempty prefix pays the genuine same-domain typed raw edge. -/
def rawPathBit (S : Signature) (K : List Ty) (Γ : List Ty) (τ : Ty) :
    NTerm → List RawHop → NTerm → Bool
  | Q, [], R => termEq Q R && finiteWindowBit S K Γ τ Q
  | Q, e :: es, R =>
    finiteWindowWitnessBit S K Γ τ e.witness Q e.target &&
      rawPathBit S K Γ τ e.target es R

end LogicLineages.PersistentMarking.NumberedWindowPathWitnessBits
