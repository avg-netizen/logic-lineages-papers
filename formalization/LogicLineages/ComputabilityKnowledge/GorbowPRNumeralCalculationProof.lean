module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiationProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations
open GorbowPRChildTags GorbowTheoryProof GorbowSubstitution List.Vector

private theorem substituteCall {ctx out arity : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private def numSub {m : Nat} (v : List.Vector Nat m) : Fin m → Term 0 :=
  fun i => Term.numeral (v.get i)

private theorem mapOfFn {alpha beta : Type} {m : Nat} (f : alpha → beta) (g : Fin m → alpha) :
    (List.Vector.ofFn g).map f = List.Vector.ofFn (fun i => f (g i)) := by
  apply List.Vector.ext
  intro i
  simp

private theorem subArguments {m : Nat} (v : List.Vector Nat m) :
    (argumentVariables m).map (substitute (numSub v)) = numeralArguments v := by
  apply List.Vector.ext
  intro i
  simp [argumentVariables, numSub, numeralArguments, substitute]

private theorem subTail {m : Nat} (k : Nat) (v : List.Vector Nat m) :
    (tailVariables m).map (substitute (Fin.cases (Term.numeral k) (numSub v))) =
      numeralArguments v := by
  apply List.Vector.ext
  intro i
  simp [tailVariables, numSub, numeralArguments, substitute]

private theorem nodeMember {n m : Nat} (p : Program n) (tag : Nat) (q : Program m)
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (sigma : Sentence)
    (hs : sigma ∈ nodeEquations q tag) : sigma ∈ axioms p := by
  have hb : tag < (nodes p).length := by
    by_contra hn
    have he := List.getElem?_eq_none (l:=nodes p) (Nat.le_of_not_gt hn)
    rw [ht] at he
    cases he
  have helem : (nodes p)[tag] = ⟨m,q⟩ := by simpa [hb] using ht
  apply List.mem_flatMap.mpr
  refine ⟨(⟨m,q⟩,tag), ?_, hs⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨tag, by simpa using hb, ?_⟩
  simp [helem]

private theorem equationInstance {n m ctx : Nat} (p : Program n) (tag : Nat) (q : Program m)
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (lhs rhs : Term ctx)
    (he : equation lhs rhs ∈ nodeEquations q tag) (sigma : Fin ctx → Term 0) :
    Nonempty (Derivation (Theory p) (.equal (substitute sigma lhs) (substitute sigma rhs))) := by
  exact GorbowUniversalInstantiation.Proof.axiomSpecialization (Theory p) ctx
    (.equal lhs rhs) sigma (nodeMember p tag q ht _ he)

private theorem childLookup {n m : Nat} (p : Program n) (tag : Nat) (q : Program m)
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (localTag : Nat) (a : Packed)
    (hl : (nodes q)[localTag]? = some a) : (nodes p)[tag+localTag]? = some a :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m,q⟩ localTag a ht hl

private theorem calculate {m : Nat} (q : Program m) :
    ∀ n (p : Program n) (tag : Nat), (nodes p)[tag]? = some ⟨m,q⟩ →
    ∀ v : List.Vector Nat m, Nonempty (Derivation (Theory p)
      (.equal (call tag (numeralArguments v)) (Term.numeral (evaluate q v)))) := by
  induction q with
  | zero =>
      intro n p tag ht v
      have hv : v = List.Vector.nil := by apply List.Vector.ext; intro i; exact Fin.elim0 i
      subst v
      have h := equationInstance p tag .zero ht (call tag List.Vector.nil) .zero
        (by simp [nodeEquations]) (Fin.elim0 : Fin 0 → Term 0)
      simpa only [substituteCall, List.Vector.map_nil,
        substitute, numeralArguments, evaluate, Term.numeral] using h
  | succ =>
      intro n p tag ht v
      have h := equationInstance p tag .succ ht (call tag (argumentVariables 1)) (.succ (.var 0))
        (by simp [nodeEquations]) (numSub v)
      simpa only [substituteCall, subArguments, substitute,
        numSub, evaluate, List.Vector.get_zero, Term.numeral] using h
  | projection i =>
      intro n p tag ht v
      have h := equationInstance p tag (.projection i) ht (call tag (argumentVariables _)) (.var i)
        (by simp [nodeEquations]) (numSub v)
      simpa only [substituteCall, subArguments, substitute,
        numSub, evaluate] using h
  | @composition m k f g ihf ihg =>
      intro n p tag ht v
      have hf := childLookup p tag (.composition f g) ht 1 ⟨k,f⟩
        (GorbowPRChildTags.Proof.compositionFunction m k f g)
      have hg : ∀ i, (nodes p)[tag+argumentTag f g i]? = some ⟨m,g i⟩ :=
        fun i => childLookup p tag (.composition f g) ht _ _
          (GorbowPRChildTags.Proof.compositionArgument m k f g i)
      have he := equationInstance p tag (.composition f g) ht (call tag (argumentVariables m))
        (call (tag+1) (List.Vector.ofFn fun i => call (tag+argumentTag f g i) (argumentVariables m)))
        (by simp [nodeEquations]) (numSub v)
      simp only [substituteCall, subArguments, mapOfFn] at he
      let values : List.Vector Nat k := List.Vector.ofFn fun i => evaluate (g i) v
      have hc := GorbowPRCallCongruence.Proof.callCongruence (Theory p) k (tag+1)
        (List.Vector.ofFn fun i => call (tag+argumentTag f g i) (numeralArguments v))
        (numeralArguments values) (fun i => by
          simpa [values, numeralArguments] using ihg i n p _ (hg i) v)
      obtain ⟨pe⟩ := he
      obtain ⟨pc⟩ := hc
      obtain ⟨pf⟩ := ihf n p (tag+1) hf values
      obtain ⟨pec⟩ := GorbowTheoryEqualityProof.transitivity (Theory p) _ _ _ pe pc
      exact GorbowTheoryEqualityProof.transitivity (Theory p) _ _ _ pec pf
  | @recursion k f g ihf ihg =>
      intro n p tag ht v
      have hf := childLookup p tag (.recursion f g) ht 1 ⟨k,f⟩
        (GorbowPRChildTags.Proof.recursionBase k f g)
      have hg := childLookup p tag (.recursion f g) ht (stepTag f) ⟨k+2,g⟩
        (GorbowPRChildTags.Proof.recursionStep k f g)
      have hrec : ∀ y (xs : List.Vector Nat k), Nonempty (Derivation (Theory p)
          (.equal (call tag (numeralArguments (y ::ᵥ xs)))
            (Term.numeral (evaluate (.recursion f g) (y ::ᵥ xs))))) := by
        intro y
        induction y with
        | zero =>
            intro xs
            have he := equationInstance p tag (.recursion f g) ht
              (call tag (.zero ::ᵥ argumentVariables k)) (call (tag+1) (argumentVariables k))
              (by simp [nodeEquations]) (numSub xs)
            simp only [substituteCall, List.Vector.map_cons,
              substitute, subArguments] at he
            obtain ⟨pe⟩ := he
            obtain ⟨pf⟩ := ihf n p (tag+1) hf xs
            have h := GorbowTheoryEqualityProof.transitivity (Theory p) _ _ _ pe pf
            simpa only [numeralArguments, List.Vector.map_cons, Term.numeral,
              evaluate, List.Vector.head_cons, List.Vector.tail_cons, Nat.rec_zero] using h
        | succ y ih =>
            intro xs
            have he := equationInstance p tag (.recursion f g) ht
              (call tag (.succ (.var 0) ::ᵥ tailVariables k))
              (call (tag+stepTag f)
                (.var 0 ::ᵥ call tag (.var 0 ::ᵥ tailVariables k) ::ᵥ tailVariables k))
              (by simp [nodeEquations]) (Fin.cases (Term.numeral y) (numSub xs))
            simp only [substituteCall, List.Vector.map_cons,
              substitute, Fin.cases_zero, subTail] at he
            let previous := evaluate (.recursion f g) (y ::ᵥ xs)
            have hc := GorbowPRCallCongruence.Proof.callCongruence (Theory p) (k+2) (tag+stepTag f)
              (Term.numeral y ::ᵥ call tag (Term.numeral y ::ᵥ numeralArguments xs) ::ᵥ numeralArguments xs)
              (numeralArguments (y ::ᵥ previous ::ᵥ xs)) (fun i => by
                cases i using Fin.cases with
                | zero => exact ⟨.logical (.reflexive _)⟩
                | succ i =>
                    cases i using Fin.cases with
                    | zero =>
                        change Nonempty (Derivation (Theory p) (.equal
                          (call tag (Term.numeral y ::ᵥ numeralArguments xs)) (Term.numeral previous)))
                        exact ih xs
                    | succ i => exact ⟨.logical (.reflexive _)⟩)
            obtain ⟨pe⟩ := he
            obtain ⟨pc⟩ := hc
            obtain ⟨pg⟩ := ihg n p (tag+stepTag f) hg (y ::ᵥ previous ::ᵥ xs)
            obtain ⟨pec⟩ := GorbowTheoryEqualityProof.transitivity (Theory p) _ _ _ pe pc
            have h := GorbowTheoryEqualityProof.transitivity (Theory p) _ _ _ pec pg
            simpa only [numeralArguments, List.Vector.map_cons, Term.numeral, previous,
              evaluate, List.Vector.head_cons, List.Vector.tail_cons, Nat.rec_add_one] using h
      rcases v with ⟨values, hvalues⟩
      cases values with
      | nil => simp at hvalues
      | cons head tail =>
          have htail : tail.length = k := by simpa using hvalues
          exact hrec head ⟨tail,htail⟩

theorem numeralCalculation : Targets.NumeralCalculation := by
  intro n p tag m q ht v
  exact calculate q n p tag ht v

theorem numeralExactness : Targets.NumeralExactness := by
  intro n p tag m q ht v value
  constructor
  · rintro ⟨proof⟩
    let I : Interpretation := ⟨fun _ => False, fun _ => 0, fun _ => False,
      fun _ => False, fun _ _ => False, fun _ => False⟩
    have h := GorbowPRDefiningEquations.Proof.theorySoundness n p _ proof I
    change (call tag (numeralArguments v)).realize (interpretation p I) Fin.elim0 =
      (Term.numeral value).realize (interpretation p I) Fin.elim0 at h
    rw [GorbowPRDefiningEquations.Proof.termCalibration 0 n p tag m q
      (numeralArguments v) I Fin.elim0 ht, numeral_realize] at h
    have hv : (numeralArguments v).map (fun t => t.realize (interpretation p I) Fin.elim0) = v := by
      apply List.Vector.ext
      intro i
      simp [numeralArguments, numeral_realize]
    simpa only [hv] using h
  · intro h
    simpa only [h] using numeralCalculation n p tag m q ht v

end LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.Proof
