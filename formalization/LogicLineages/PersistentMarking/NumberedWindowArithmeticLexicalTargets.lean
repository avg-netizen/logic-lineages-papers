import LogicLineages.PersistentMarking.NumberedWindowLexicalAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalTargets
open Spine NumberedWindowSyntax NumberedWindowTypingBits NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowLexicalAlgorithm

def codeLookup (C : BoundContext) (i : Nat) := (C i).map encodeTy

def LiteralLexicalRequirements : Prop :=
  (∀ (C : BoundContext) q, holds (codeLookup C) (requirements (encodeTerm q)).1 = termOK C q) ∧
  (∀ (C : BoundContext) qs, holds (codeLookup C) (requirements (encodeArgs qs)).2 = argsOK C qs)

def ExactFiniteTypedChecker : Prop := ∀ (Γ : List Ty) τ n,
  typed (Γ.map encodeTy) (encodeTy τ) n = (decodeTerm n).any (typedBit (binderLookup Γ) τ)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalTargets
