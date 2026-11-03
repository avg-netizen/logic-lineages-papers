module

public import LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquationsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquations.Proof
open GorbowSyntax GorbowTheoryProof GorbowStandardInduction GorbowStandardInstances
open GorbowFormulaSubstitution GorbowPRProgram GorbowPRRegistry
open GorbowPRDefiningEquations GorbowPRNumeralCalculation GorbowPRChildTags
open GorbowSubstitution List.Vector

private theorem instantiate_lift {n ctx : Nat} (phi : Formula (n+1))
    (sigma : Fin (n+1) → Term ctx) :
    instantiate (substituteFormula (liftSubstitute fun i => sigma i.succ) phi) (sigma 0)=
      symbolicInstance phi sigma := by
  unfold instantiate symbolicInstance
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [liftSubstitute,Fin.cases_succ,renameTerm]
    rw [GorbowSubstitution.substitute_composition]
    have he : (fun j : Fin ctx => GorbowSubstitution.substitute
        (Fin.cases (sigma 0) Term.var) (Term.var j.succ))=Term.var := by
      funext j
      rfl
    rw [he]
    exact GorbowSubstitution.substitute_variables (sigma i.succ)

theorem openAxiomSpecialization : Targets.OpenAxiomSpecialization := by
  intro A n
  induction n with
  | zero =>
    intro ctx phi sigma h
    have hs : sigma=(Fin.elim0 : Fin 0 → Term ctx) := by funext i; exact Fin.elim0 i
    subst sigma
    exact ⟨Derivation.axiom phi h⟩
  | succ n ih =>
    intro ctx phi sigma h
    obtain ⟨q⟩ := ih ctx (.all phi) (fun i => sigma i.succ) h
    change Derivation A (.all (substituteFormula (liftSubstitute fun i => sigma i.succ) phi)) at q
    have r := Derivation.mp (Derivation.logical (A:=A)
      (.allInstantiate (substituteFormula (liftSubstitute fun i => sigma i.succ) phi) (sigma 0))) q
    exact ⟨by simpa only [instantiate_lift] using r⟩

/-- The finite node membership argument is the same actual zip-index lookup
used by the accepted numeral-calculation supplier; no equation is postulated. -/
private theorem node_member {n m : Nat} (p : Program n) (tag : Nat) (q : Program m)
    (ht : (nodes p)[tag]?=some ⟨m,q⟩) (sigma : Sentence)
    (hs : sigma ∈ nodeEquations q tag) : sigma ∈ axioms p := by
  have hb : tag < (nodes p).length := by
    by_contra hn
    have he := List.getElem?_eq_none (l:=nodes p) (Nat.le_of_not_gt hn)
    rw [ht] at he
    cases he
  have helem : (nodes p)[tag]=⟨m,q⟩ := by simpa [hb] using ht
  apply List.mem_flatMap.mpr
  refine ⟨(⟨m,q⟩,tag),?_,hs⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨tag,by simpa using hb,?_⟩
  simp [helem]

theorem nodeEquationInstances : Targets.NodeEquationInstances := by
  intro n p tag m q ht arity ctx lhs rhs he sigma
  exact openAxiomSpecialization (Theory p) arity ctx (.equal lhs rhs) sigma
    (node_member p tag q ht _ he)

private theorem sub_call {arity ctx out : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args)=call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem sub_arguments {arity ctx : Nat} (args : List.Vector (Term ctx) arity) :
    (argumentVariables arity).map (substitute args.get)=args := by
  apply List.Vector.ext
  intro i
  simp [argumentVariables,substitute]

private theorem map_ofFn {alpha beta : Type} {m : Nat} (f : alpha → beta) (g : Fin m → alpha) :
    (List.Vector.ofFn g).map f=List.Vector.ofFn (fun i => f (g i)) := by
  apply List.Vector.ext
  intro i
  simp

private theorem sub_tail {m ctx : Nat} (x : Term ctx) (args : List.Vector (Term ctx) m) :
    (tailVariables m).map (substitute (Fin.cases x args.get))=args := by
  apply List.Vector.ext
  intro i
  simp [tailVariables,substitute]

theorem compositionEquation : Targets.CompositionEquation := by
  intro n p tag m k f g ht ctx args
  have h := nodeEquationInstances n p tag m (.composition f g) ht m ctx
    (call tag (argumentVariables m))
    (call (tag+1) (List.Vector.ofFn fun i => call (tag+argumentTag f g i) (argumentVariables m)))
    (by simp [nodeEquations]) args.get
  simpa only [sub_call,sub_arguments,map_ofFn] using h

theorem recursionZeroEquation : Targets.RecursionZeroEquation := by
  intro n p tag m f g ht ctx args
  have h := nodeEquationInstances n p tag (m+1) (.recursion f g) ht m ctx
    (call tag (.zero ::ᵥ argumentVariables m)) (call (tag+1) (argumentVariables m))
    (by simp [nodeEquations]) args.get
  simpa only [sub_call,List.Vector.map_cons,substitute,sub_arguments] using h

theorem recursionSuccessorEquation : Targets.RecursionSuccessorEquation := by
  intro n p tag m f g ht ctx x args
  have h := nodeEquationInstances n p tag (m+1) (.recursion f g) ht (m+1) ctx
    (call tag (.succ (.var 0) ::ᵥ tailVariables m))
    (call (tag+stepTag f) (.var 0 ::ᵥ call tag (.var 0 ::ᵥ tailVariables m) ::ᵥ tailVariables m))
    (by simp [nodeEquations]) (Fin.cases x args.get)
  simpa only [sub_call,List.Vector.map_cons,substitute,Fin.cases_zero,sub_tail] using h

end LogicLineages.ComputabilityKnowledge.GorbowPRSymbolicEquations.Proof
