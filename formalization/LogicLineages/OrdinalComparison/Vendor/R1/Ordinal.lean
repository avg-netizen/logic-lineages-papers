module
public import Mathlib.SetTheory.Ordinal.Notation
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
# Normal-form arithmetic for the pure R1 endpoint calculator

`endpoint` computes the Cantor-normal-form recurrence for the endpoint below
epsilon zero. Coefficients remain compressed; multiplication by a natural is
on the right. `principalSummands` expands coefficients only in the specification.

The theorems below concern normality and genuine `Ordinal` denotation. They do
not themselves define recursive Sigma-one elementarity. The semantic
identification is proved in this package's `Correctness.lean`, reconstructing
Carlson's characterization and the endpoint recursion displayed by Wilken,
*Pure Sigma2-Elementarity beyond the Core*, Proposition 1.1.
-/

namespace LogicLineages.OrdinalComparison.Vendor.R1

open ONote

/-- The final exponent of a Cantor-normal-form notation; zero is assigned zero. -/
def lastExponent : ONote → ONote
  | .zero => 0
  | .oadd e _ .zero => e
  | .oadd _ _ a => lastExponent a

/-- Sum of the endpoints of the principal summands, retaining natural coefficients.
`ONote.mulNat u n` denotes `u * n`, not `n * u`. -/
def principalSum : ONote → ONote
  | .zero => 0
  | .oadd e n a =>
      ONote.mulNat (.oadd e 1 0 + principalSum e) (n : ℕ) + principalSum a

/-- The arithmetic endpoint recurrence, defined structurally on raw syntax. -/
def endpoint (a : ONote) : ONote :=
  a + principalSum (lastExponent a)

/-- Principal summands in order, expanded only for the mathematical specification. -/
def principalSummands : ONote → List ONote
  | .zero => []
  | .oadd e n a => List.replicate (n : ℕ) (.oadd e 1 0) ++ principalSummands a

@[simp] theorem lastExponent_zero : lastExponent 0 = 0 := rfl
@[simp] theorem principalSum_zero : principalSum 0 = 0 := rfl
@[simp] theorem endpoint_zero : endpoint 0 = 0 := rfl
@[simp] theorem principalSummands_zero : principalSummands 0 = [] := rfl

@[simp] theorem lastExponent_principal (e : ONote) :
    lastExponent (.oadd e 1 0) = e := rfl

theorem lastExponent_nf : ∀ {a : ONote}, NF a → NF (lastExponent a)
  | .zero, _ => NF.zero
  | .oadd _ _ a, h => by
      cases a with
      | zero => exact h.fst
      | oadd e n b => exact lastExponent_nf (a := .oadd e n b) h.snd

theorem principalSum_nf : ∀ {a : ONote}, NF a → NF (principalSum a)
  | .zero, _ => NF.zero
  | .oadd e _ a, h => by
      haveI : NF e := h.fst
      haveI : NF (principalSum e) := principalSum_nf h.fst
      haveI : NF (principalSum a) := principalSum_nf h.snd
      exact ONote.add_nf _ _

theorem endpoint_nf {a : ONote} (h : NF a) : NF (endpoint a) := by
  haveI : NF a := h
  haveI : NF (principalSum (lastExponent a)) :=
    principalSum_nf (lastExponent_nf h)
  exact ONote.add_nf _ _

/-- Public executable endpoint on intrinsically normal input, with normal output. -/
def endpointNF (a : NONote) : NONote :=
  ⟨endpoint a.1, endpoint_nf a.2⟩

@[simp] theorem endpointNF_val (a : NONote) :
    (endpointNF a).1 = endpoint a.1 := rfl

theorem principalSummands_nf : ∀ {a : ONote}, NF a →
    ∀ r ∈ principalSummands a, NF r
  | .zero, _, _, h => by simp [principalSummands] at h
  | .oadd e _ a, h, r, hr => by
      haveI : NF e := h.fst
      simp only [principalSummands, List.mem_append, List.mem_replicate] at hr
      rcases hr with ⟨_, rfl⟩ | hr
      · infer_instance
      · exact principalSummands_nf h.snd r hr

/-- Expanding coefficients preserves the ordinal denotation and its addition order. -/
theorem principalSummands_repr : ∀ a : ONote,
    a.repr = ((principalSummands a).map ONote.repr).sum
  | .zero => by simp [principalSummands]
  | .oadd e n a => by
      simp only [principalSummands, List.map_append, List.map_replicate,
        List.sum_append, List.sum_replicate, Ordinal.nsmul_eq_mul]
      rw [← principalSummands_repr a]
      simp [ONote.repr]

theorem endpoint_principal_repr (e : ONote) (h : NF e) :
    (endpoint (.oadd e 1 0)).repr =
      (ONote.oadd e 1 0).repr + (principalSum e).repr := by
  haveI : NF e := h
  haveI : NF (principalSum e) := principalSum_nf h
  change (.oadd e 1 0 + principalSum e).repr = _
  exact ONote.repr_add _ _

/-- Compressed right-natural multiplication equals the ordered sum of endpoints
of the expanded principal summands. This is an equality in `Ordinal`. -/
theorem principalSum_repr : ∀ {a : ONote}, NF a →
    (principalSum a).repr =
      ((principalSummands a).map (fun r => (endpoint r).repr)).sum
  | .zero, _ => by simp [principalSum, principalSummands]
  | .oadd e n a, h => by
      haveI : NF e := h.fst
      haveI : NF a := h.snd
      haveI : NF (principalSum e) := principalSum_nf h.fst
      haveI : NF (principalSum a) := principalSum_nf h.snd
      calc
        (principalSum (.oadd e n a)).repr =
            ((ONote.oadd e 1 0).repr + (principalSum e).repr) * (n : ℕ) +
              (principalSum a).repr := by
          simp only [principalSum, ONote.mulNat_eq_mul, ONote.repr_add,
            ONote.repr_mul, ONote.repr_ofNat]
        _ = (endpoint (.oadd e 1 0)).repr * (n : ℕ) +
            ((principalSummands a).map (fun r => (endpoint r).repr)).sum := by
          rw [endpoint_principal_repr e h.fst, principalSum_repr h.snd]
        _ = ((principalSummands (.oadd e n a)).map
            (fun r => (endpoint r).repr)).sum := by
          simp only [principalSummands, List.map_append, List.map_replicate,
            List.sum_append, List.sum_replicate, Ordinal.nsmul_eq_mul]

/-- Wilken's endpoint recursion in ordinal denotation, with the zero case included.
The semantic identification with pure R1 is not assumed by this theorem. -/
theorem endpoint_recursion {a : ONote} (h : NF a) :
    (endpoint a).repr = a.repr +
      ((principalSummands (lastExponent a)).map (fun r => (endpoint r).repr)).sum := by
  haveI : NF a := h
  haveI : NF (principalSum (lastExponent a)) :=
    principalSum_nf (lastExponent_nf h)
  rw [endpoint, ONote.repr_add, principalSum_repr (lastExponent_nf h)]

theorem endpointNF_recursion (a : NONote) :
    (endpointNF a).repr = a.repr +
      ((principalSummands (lastExponent a.1)).map (fun r => (endpoint r).repr)).sum :=
  endpoint_recursion a.2

theorem repr_le_endpoint {a : ONote} (h : NF a) :
    a.repr ≤ (endpoint a).repr := by
  rw [endpoint_recursion h]
  exact le_self_add

/-- Decidable arithmetic interval test. Its interpretation as pure R1 uses
the separately cited semantic theorem; the implementation uses normal forms. -/
def intervalCheck (a b : NONote) : Bool :=
  decide (a ≤ b ∧ b ≤ endpointNF a)

theorem intervalCheck_correct (a b : NONote) :
    intervalCheck a b = true ↔ a.repr ≤ b.repr ∧ b.repr ≤ (endpointNF a).repr := by
  simp only [intervalCheck, decide_eq_true_eq]
  rfl

example : endpoint 1 = 1 := by decide
example : endpoint ONote.omega = ONote.omega + 1 := by decide
example : endpoint (.oadd (ONote.ofNat 2) 1 0) =
    .oadd (ONote.ofNat 2) 1 (ONote.ofNat 2) := by decide
-- This coefficient case distinguishes right-natural multiplication:
-- (omega + 1) * 2 = omega * 2 + 1.
example : principalSum (.oadd 1 2 0) = .oadd 1 2 1 := by decide
example : intervalCheck (NONote.mk (.oadd 1 1 0))
    (NONote.mk (ONote.oadd 1 1 0 + 1)) = true := by decide

#print axioms principalSum_nf
#print axioms principalSum_repr
#print axioms endpoint_recursion
#print axioms intervalCheck_correct

end LogicLineages.OrdinalComparison.Vendor.R1
