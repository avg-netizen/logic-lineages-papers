module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeRowsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.NarendranSimultaneousProof
public import Mathlib.Tactic.LinearCombination
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitGadgetTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
open Polynomial Narendran

private theorem signed_natCast (n : Nat) : signed (n : NPolynomial) = C (n : Int) := by
  simp [signed]


/-- These are the literal three rows, with the same designated shared four
witness wires. There is no fresh existential choice at each occurrence. -/
theorem square_rows_equations (p : Nat → NPolynomial) (u v aux U V : Nat)
    (hu : p u=C U) (hv : p v=C V) :
    RowsSolve p (squareRows u v aux) ↔
      SquareGadget U V (fun i : Fin 4 => p (aux+i.val)) := by
  constructor
  · intro h
    have h1 := h _ (show
      [wireMonomial 1 1 aux,wireMonomial (-1) 0 aux,wireMonomial (-1) 0 (aux+3),constant 1]
        ∈ squareRows u v aux from by simp [squareRows])
    have h2 := h _ (show
      [wireMonomial 1 1 (aux+1),wireMonomial (-1) 0 (aux+1),wireMonomial (-1) 0 aux,wireMonomial 1 0 u]
        ∈ squareRows u v aux from by simp [squareRows])
    have h3 := h _ (show
      [wireMonomial 1 1 (aux+2),wireMonomial (-1) 0 (aux+2),wireMonomial (-1) 0 (aux+1),wireMonomial 1 0 v]
        ∈ squareRows u v aux from by simp [squareRows])
    norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hu,hv,
      Narendran.Proof.signed_C,signed_natCast] at h1 h2 h3
    change (X-1)*signed (p aux)=signed (p (aux+3))-1 ∧
      (X-1)*signed (p (aux+1))=signed (p aux)-C (U : Int) ∧
      (X-1)*signed (p (aux+2))=signed (p (aux+1))-C (V : Int)
    refine ⟨?_,?_,?_⟩
    · linear_combination h1
    · simp only [Polynomial.C_eq_natCast] at h2 ⊢
      linear_combination h2
    · simp only [Polynomial.C_eq_natCast] at h3 ⊢
      linear_combination h3
  · intro h
    change (X-1)*signed (p aux)=signed (p (aux+3))-1 ∧
      (X-1)*signed (p (aux+1))=signed (p aux)-C (U : Int) ∧
      (X-1)*signed (p (aux+2))=signed (p (aux+1))-C (V : Int) at h
    obtain ⟨h1,h2,h3⟩ := h
    intro r hr
    simp only [squareRows,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hu,hv,
      Narendran.Proof.signed_C,signed_natCast]
    · linear_combination h1
    · simp only [Polynomial.C_eq_natCast] at h2 ⊢
      linear_combination h2
    · simp only [Polynomial.C_eq_natCast] at h3 ⊢
      linear_combination h3

theorem triangular_identity (n : Nat) : 2*triangularNat n+n=n^2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [triangularNat]; nlinarith

theorem triangular_addition (x y : Nat) :
    triangularNat (x+y)=triangularNat x+triangularNat y+x*y := by
  nlinarith [triangular_identity x,triangular_identity y,triangular_identity (x+y)]

/-- The two linear scalar rows plus the three triangular gadgets force a
product, although no product of polynomial unknowns occurs in any input row. -/
theorem triangular_multiplication (x y out v1 v2 v3 : Nat)
    (h1 : 2*v1+x=x^2) (h2 : 2*v2+y=y^2) (h3 : 2*v3+(x+y)=(x+y)^2)
    (hout : v3=v1+v2+out) : out=x*y := by
  nlinarith

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
