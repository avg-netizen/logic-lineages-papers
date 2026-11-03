module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecSupportProof
open Source NumberedRewriteReduction NumberedPrimaryClassPrimrec

local instance {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} : DecidableEq (Packed Symbol arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

theorem vertexListCalibration {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q : Packed Symbol arity Gamma) :
    (vertexList symbols S q).toFinset = NumberedFinitePrimaryClass.vertices symbols S q := by
  simp [vertexList, NumberedFinitePrimaryClass.vertices]

theorem stepCalibration {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q : Packed Symbol arity Gamma) (reached : List (Packed Symbol arity Gamma)) :
    (step symbols S (vertexList symbols S q) reached).toFinset =
      NumberedFinitePrimaryClass.reachStep symbols S q reached.toFinset := by
  apply Finset.ext
  intro r
  simp [step, vertexList, NumberedFinitePrimaryClass.reachStep,
    NumberedFinitePrimaryClass.vertices, List.any_eq_true]

theorem reachableListCalibration : NumberedPrimaryClassPrimrecTargets.ActualReachableListCalibration := by
  intro Symbol inst arity symbols S Gamma q fuel
  induction fuel with
  | zero => simp [reachableList, NumberedFinitePrimaryClass.reachable]
  | succ fuel ih =>
    simp only [reachableList, Function.iterate_succ_apply', NumberedFinitePrimaryClass.reachable]
    rw [stepCalibration]
    exact congrArg (NumberedFinitePrimaryClass.reachStep symbols S q) ih

theorem reachableAfterCard {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q : Packed Symbol arity Gamma) (extra : Nat) :
    NumberedFinitePrimaryClass.reachable symbols S q
        ((NumberedFinitePrimaryClass.vertices symbols S q).card + extra) =
      NumberedFinitePrimaryClass.primaryClass symbols S q := by
  induction extra with
  | zero => simp only [Nat.add_zero, NumberedFinitePrimaryClass.primaryClass]
  | succ extra ih =>
    rw [Nat.add_succ, NumberedFinitePrimaryClass.reachable, ih]
    exact NumberedFinitePrimaryClassProof.cardinalitySaturation
      Symbol inferInstance arity symbols S Gamma q

theorem primaryListCalibration : NumberedPrimaryClassPrimrecTargets.ActualPrimaryListCalibration := by
  intro Symbol inst arity symbols S Gamma q
  have hbound : (NumberedFinitePrimaryClass.vertices symbols S q).card ≤
      (vertexList symbols S q).length := by
    rw [← vertexListCalibration symbols S q]
    exact List.toFinset_card_le (l := vertexList symbols S q)
  have hlength : (vertexList symbols S q).length =
      (NumberedFinitePrimaryClass.vertices symbols S q).card +
        ((vertexList symbols S q).length -
          (NumberedFinitePrimaryClass.vertices symbols S q).card) := by omega
  unfold primaryList
  rw [reachableListCalibration Symbol inst arity symbols S Gamma q, hlength]
  exact reachableAfterCard symbols S q _

theorem primaryTestCalibration {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (q r : Packed Symbol arity Gamma) :
    decide (r ∈ primaryList symbols S q) =
      NumberedFinitePrimaryClass.primaryTest symbols S q r := by
  simp only [NumberedFinitePrimaryClass.primaryTest,
    ← primaryListCalibration Symbol inferInstance arity symbols S Gamma q,
    List.mem_toFinset]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecSupportProof
