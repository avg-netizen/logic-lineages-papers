module
public import Mathlib.Computability.PartrecCode

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedDeciderSpecialization
open Nat.Partrec (Code)

/-- Exact index specialization of a joint program. The payload is a natural
code so preexisting encodings need not be changed. The equality is in Part,
not a comparison after assigning a default to nontermination. -/
def Specializes (joint : Nat →. Nat) (compile : Code → Code) : Prop :=
  Primrec compile ∧ ∀ (e : Code) (x : Nat),
    Code.eval (compile e) x = joint (Nat.pair (Encodable.encode e) x)

/-- If a single genuine partial-recursive program on the joint inputs is
provided, a primitive-recursive function specializes it by policy index. -/
def JointProgramIndexSpecialization : Prop :=
  ∀ joint : Nat →. Nat, Nat.Partrec joint → ∃ compile : Code → Code, Specializes joint compile

/-- Particular consequence for a successful answer contract on admitted
inputs. No totality claim is made on other indices or inputs. -/
def JointAnswerIndexSpecialization : Prop :=
  ∀ (joint : Nat →. Nat) (admitted : Code → Nat → Prop) (answer : Code → Nat → Bool),
    Nat.Partrec joint →
    (∀ e x, admitted e x →
      joint (Nat.pair (Encodable.encode e) x) = Part.some (Encodable.encode (answer e x))) →
    ∃ compile : Code → Code, Primrec compile ∧
      ∀ e x, admitted e x → Code.eval (compile e) x = Part.some (Encodable.encode (answer e x))

end LogicLineages.StandardControlCurrent.PolicyIndexedDeciderSpecialization
