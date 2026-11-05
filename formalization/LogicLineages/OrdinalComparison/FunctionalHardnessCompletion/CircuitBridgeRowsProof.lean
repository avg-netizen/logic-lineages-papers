module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgePolynomialProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeWellFormedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
open Polynomial Narendran SourcePolynomialRealization

private theorem monomial_code_value (n : Nat) (p : Nat → NPolynomial)
    (m : MonomialCode) (q : SignedPair.Monomial n) (hq : monomialOfCode n m=some q) :
    C q.coefficient*X^q.power*(match q.unknown with | none => 1 | some i => signed (p i.val))=
      monomialPolynomial p m := by
  rcases m with ⟨c,k,u⟩
  cases u with
  | none =>
      simp only [monomialOfCode,Option.some.injEq] at hq
      subst q
      rfl
  | some i =>
      by_cases hi : i<n
      · simp only [monomialOfCode,hi,dif_pos,Option.some.injEq] at hq
        subst q
        rfl
      · simp [monomialOfCode,hi] at hq

private theorem monomial_exists (n : Nat) (m : MonomialCode)
    (hm : ∀ i,m.2.2=some i→i<n) : ∃ q,monomialOfCode n m=some q := by
  cases hu : m.2.2 with
  | none =>
      exact ⟨⟨m.1,m.2.1,none⟩,by simp [monomialOfCode,hu]⟩
  | some i =>
      have hi := hm i hu
      exact ⟨⟨m.1,m.2.1,some ⟨i,hi⟩⟩,by simp [monomialOfCode,hu,hi]⟩

/-- Filtering the checked finite-index codec removes no occurrence from a
well-formed row. All original occurrences still read the same p(i). -/
theorem row_interpret (n : Nat) (p : Nat → NPolynomial) : ∀ r : Row,
    (∀ m∈r,∀ i,m.2.2=some i→i<n) →
    expressionPolynomial (fun i : Fin n => signed (p i.val))
      (SignedPair.fromMonomials (r.filterMap (monomialOfCode n)))=rowPolynomial p r := by
  intro r
  rw [fromMonomials_polynomial]
  induction r with
  | nil => intro _; rfl
  | cons m ms ih =>
      intro hr
      obtain ⟨q,hq⟩ := monomial_exists n m (hr m (List.mem_cons_self))
      have ht : ∀ q∈ms,∀ i,q.2.2=some i→i<n :=
        fun q hq => hr q (List.mem_cons_of_mem m hq)
      simp only [List.filterMap_cons,hq,List.map_cons,List.sum_cons]
      calc
        _ = monomialPolynomial p m + rowPolynomial p ms :=
          congrArg₂ (fun a b : ZPolynomial => a + b) (monomial_code_value n p m q hq) (ih ht)
        _ = rowPolynomial p (m :: ms) := rfl

/-- The raw polynomial-system reading and the exact shared Finsupp source
problem are equivalent. Malformed systems are handled separately by the
frozen input predicate; no invalid reference is silently used as zero. -/
theorem raw_system_faithful (c : SystemCode) (hc : WellFormedCode c) :
    PolynomialSatisfiable (systemOfCode c) ↔ ∃ p : Nat → NPolynomial,RowsSolve p c.2 := by
  constructor
  · rintro ⟨p,hp⟩
    let q : Nat → NPolynomial := fun i => if hi : i<c.1 then Polynomial.ofFinsupp (p ⟨i,hi⟩) else 0
    have hq : ∀ i : Fin c.1,(q i.val).toFinsupp=p i := by
      intro i
      simp [q,i.isLt]
    have hsol : PolynomialSolves (systemOfCode c) (fun i => (q i.val).toFinsupp) := by
      simpa only [hq] using hp
    have heval := (system_zero_iff (fun i : Fin c.1 => q i.val) (systemOfCode c)).mp hsol
    refine ⟨q,?_⟩
    intro r hr
    have hd : SignedPair.fromMonomials (r.filterMap (monomialOfCode c.1))∈systemOfCode c :=
      List.mem_map.mpr ⟨r,hr,rfl⟩
    have he := heval _ hd
    rw [row_interpret c.1 q r (hc r hr)] at he
    exact he
  · rintro ⟨p,hp⟩
    refine ⟨fun i : Fin c.1 => (p i.val).toFinsupp,?_⟩
    apply (system_zero_iff (fun i : Fin c.1 => p i.val) (systemOfCode c)).mpr
    intro d hd
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hd
    rw [row_interpret c.1 p r (hc r hr)]
    exact hp r hr

/-- The exact well-formedness conjunct of the already frozen FullCircuitEncoding
contract. This checks the current submitted component and claims no full
circuit-solvability or numerical-encoder theorem. -/
theorem checked_circuit_wellFormed
    (c : LogicLineages.ComputabilityKnowledge.CircuitReduction.Circuit) (hc : c.WellFormed) :
    WellFormedCode (encodeCircuitSystem c) := circuit_system_wellFormed c hc

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
