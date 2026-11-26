module
public import LogicLineages.StandardControlCurrent.NumericalKernelDefinitions
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedGuards
open OrdinalComparison PolynomialGraphCompletion NumericalKernel
noncomputable def letterValue (a : Letter) (t : Nat) : Nat :=
  if a.1 = 0 then ((t : Int)+a.2.2.2).toNat
  else if a.1 = 1 then Phi t
  else if a.1 = 2 then rawQuadraticShift a.2.2.2 t
  else if a.1 = 3 then signed a.2.1 a.2.2.1 a.2.2.2 t
  else count a.2.1 a.2.2.1 t
noncomputable def LetterDomain (a : Letter) (t : Nat) : Prop :=
  if a.1 = 0 then 0 ≤ (t : Int)+a.2.2.2
  else if a.1 = 1 then True
  else if a.1 = 2 then 0 < ((Phi t/2 : Nat) : Int)+a.2.2.2+1
  else if a.1 = 3 then a.2.2.1 ≤ Phi t ∧ 0 < depth a.2.1 a.2.2.1 a.2.2.2 t
  else a.1 = 4 ∧ a.2.2.1 ≤ Phi t
noncomputable def wordValue : Word → Nat → Nat
  | [],t => t
  | a::w,t => wordValue w (letterValue a t)
noncomputable def WordDomain : Word → Nat → Prop
  | [],_ => True
  | a::w,t => LetterDomain a t ∧ WordDomain w (letterValue a t)
end LogicLineages.StandardControlCurrent.OrderedGuards
