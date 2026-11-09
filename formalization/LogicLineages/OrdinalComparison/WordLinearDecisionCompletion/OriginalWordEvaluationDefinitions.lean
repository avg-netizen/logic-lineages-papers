module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Definitions
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduledDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation
open PolynomialGraphCompletion
open LayeredComparison.SnyatkovCompletion

/-- Literal original scheduled counts, including all startup inputs. -/
noncomputable def letter (a : Letter) (t : Nat) : Nat :=
  if a.1 = 0 then ((t : Int) + a.2.2.2).toNat
  else if a.1 = 1 then Phi t
  else if a.1 = 2 then (Phi^[(((Phi t / 2 : Nat) : Int) + a.2.2.2 + 1).toNat]) t
  else if a.1 = 3 then
    (Phi^[((OriginalScheduled.sourceCount a.2.1 a.2.2.1 t : Int) + a.2.2.2).toNat]) t
  else OriginalScheduled.sourceCount a.2.1 a.2.2.1 t

/-- A Boolean domain test for the literal source letter. No tail-generated
letter or alternative scheduler is used for a small original input. -/
noncomputable def letterDomain (a : Letter) (t : Nat) : Bool :=
  if a.1 = 0 then decide (0 ≤ (t : Int) + a.2.2.2)
  else if a.1 = 1 then true
  else if a.1 = 2 then decide (0 < ((Phi t / 2 : Nat) : Int) + a.2.2.2 + 1)
  else if a.1 = 3 then
    decide (a.2.2.1 ≤ Phi t ∧
      0 < (OriginalScheduled.sourceCount a.2.1 a.2.2.1 t : Int) + a.2.2.2)
  else decide (a.1 = 4 ∧ a.2.2.1 ≤ Phi t)

noncomputable def word : Word → Nat → Nat
  | [], t => t
  | a :: w, t => word w (letter a t)

noncomputable def wordDomain : Word → Nat → Bool
  | [], _ => true
  | a :: w, t => letterDomain a t && wordDomain w (letter a t)

/-- Keep every surviving literal token, with its original coefficient/order.
All x occurrences contribute to the constant, including coefficient zero. -/
noncomputable def specializeRow (x n : Nat) (r : Row) : Row :=
  (r.1 + (r.2.map (fun a =>
      if a.2.1 = x then a.1 * (word a.2.2 n : Int) else 0)).sum,
    r.2.filter (fun a => a.2.1 != x))

noncomputable def specializeAtom (x n : Nat) : Atom → Atom
  | .nonnegative r => .nonnegative (specializeRow x n r)
  | .divisible m r => .divisible m (specializeRow x n r)

noncomputable def specialize (x n : Nat) : Formula → Formula
  | .bot => .bot
  | .top => .top
  | .atom a => .atom (specializeAtom x n a)
  | .neg p => .neg (specialize x n p)
  | .conj p q => .conj (specialize x n p) (specialize x n q)
  | .disj p q => .disj (specialize x n p) (specialize x n q)

/-- All removed original domains are checked, independent of atom truth,
Boolean polarity and branch selection. -/
noncomputable def removedDomains (x n : Nat) (p : Formula) : Bool :=
  p.tokens.all (fun t => if t.1 = x then wordDomain t.2 n else true)

namespace Code
noncomputable def specializeAtom (x n : Nat) (a : WordLinearDecisionCompletion.Code.AtomData) :
    WordLinearDecisionCompletion.Code.AtomData :=
  (a.1, a.2.1, specializeRow x n a.2.2)

noncomputable def specialize (x n code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (fun a => Encodable.encode
    (specializeAtom x n (WordLinearDecisionCompletion.Code.decodeAtom a))) code

noncomputable def removedDomains (x n code : Nat) : Bool :=
  (LinearRows.Code.atoms code).all (fun a =>
    (WordLinearDecisionCompletion.Code.decodeAtom a).2.2.2.all
      (fun b => if b.2.1 = x then wordDomain b.2.2 n else true))
end Code

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation
