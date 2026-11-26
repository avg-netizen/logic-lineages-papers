module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.GraphSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.InputProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem getLeft {α : Type} {n m : Nat} (xs : List.Vector α n) (ys : List.Vector α m) (i : Fin n) :
 (xs ++ ys).get (i.castAdd m) = xs.get i := by
 rcases xs with ⟨xs,hx⟩
 rcases ys with ⟨ys,hy⟩
 simp [List.Vector.get,List.Vector.append_def,List.get_eq_getElem,List.getElem_append_left,hx,i.isLt]

theorem getRight {α : Type} {n m : Nat} (xs : List.Vector α n) (ys : List.Vector α m) (i : Fin m) :
 (xs ++ ys).get (Fin.natAdd n i) = ys.get i := by
 rcases xs with ⟨xs,hx⟩
 rcases ys with ⟨ys,hy⟩
 simp [List.Vector.get,List.Vector.append_def,List.get_eq_getElem,List.getElem_append_right,hx,Fin.natAdd]

theorem left {α : Type} {n : Nat} (xs ys codes : List.Vector α n) (i : Fin n) :
 (pack xs ys codes).get (i.castAdd (n+n)) = xs.get i := getLeft xs (ys ++ codes) i

theorem right {α : Type} {n : Nat} (xs ys codes : List.Vector α n) (i : Fin n) :
 (pack xs ys codes).get (Fin.natAdd n (i.castAdd n)) = ys.get i :=
 (getRight xs (ys ++ codes) (i.castAdd n)).trans (getLeft ys codes i)

theorem code {α : Type} {n : Nat} (xs ys codes : List.Vector α n) (i : Fin n) :
 (pack xs ys codes).get (Fin.natAdd n (Fin.natAdd n i)) = codes.get i :=
 (getRight xs (ys ++ codes) (Fin.natAdd n i)).trans (getRight ys codes i)

theorem tail {arity inputs ctx : Nat} (p : Program arity) (q : Program inputs) (target : Term ctx)
 (args : List.Vector (Term ctx) inputs) (v : Term ctx) (h : Computes p q args v) :
 Computes p (tailProgram q) (target ::ᵥ args) v := by
 intro tag ht
 have hargs : ∀ i : Fin inputs, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call (tag + GorbowPRChildTags.argumentTag q (fun j => Program.projection j.succ) i) (target ::ᵥ args)) (args.get i))) := by
  intro i
  have hi := LiteralRawMP.ConstructorSupportProof.projection p (target ::ᵥ args) i.succ
   (tag + GorbowPRChildTags.argumentTag q (fun j => Program.projection j.succ) i)
   (Equations.argumentChild p tag q (fun j => Program.projection j.succ) ht i)
  simpa only [List.Vector.get_cons_succ] using hi
 obtain ⟨he⟩ := Equations.compositionValues p tag q (fun j => .projection j.succ) ht (target ::ᵥ args) args hargs
 obtain ⟨hq⟩ := h (tag+1) (Equations.functionChild p tag q (fun i => .projection i.succ) ht)
 exact ⟨Logic.trans _ _ _ he hq⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.InputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.InputProof
