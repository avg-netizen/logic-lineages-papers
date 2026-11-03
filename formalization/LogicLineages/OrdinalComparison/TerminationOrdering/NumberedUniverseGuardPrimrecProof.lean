module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedFiniteUniverse
open NumberedTypedRequests NumberedRequestPresentation NumberedCodeView
open NumberedRequestExpansionPrimrecSupportProof NumberedHeadWindowPrimrecProof

abbrev Window (n : Nat) := List (Fin n) × List Ty

/-- Additional root conditions beyond membership of the expected term result. -/
def extraView (n : Nat) (arity : Fin n → Nat) : Window n × CodeView n → Bool :=
  withSum (fun _ => true)
    (withSum (fun p => decide (p.2.1 ∈ p.1.2))
      (withSum (fun _ => true)
        (withSum (fun _ => true)
          (withSum (fun p => decide (HeadInWindow arity p.1.1 p.1.2 (decodeHead p.2.1)))
            (withSum (fun p => decide (HeadInWindow arity p.1.1 p.1.2 (decodeHead p.2.2.1)))
              (withSum (fun _ => true) (fun _ => true)))))))

theorem extraViewPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (extraView n arity) := by
  have hlam : Primrec (fun p : Window n × (Ty × Code (Fin n)) =>
      decide (p.2.1 ∈ p.1.2)) :=
    ((memberPrimitive Ty).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).decide
  have hord : Primrec (fun p : Window n × (HeadCode (Fin n) × Code (Fin n)) =>
      decide (HeadInWindow arity p.1.1 p.1.2 (decodeHead p.2.1))) :=
    (headWindowPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
  have hnum : Primrec (fun p : Window n × NumberedFields n =>
      decide (HeadInWindow arity p.1.1 p.1.2 (decodeHead p.2.2.1))) :=
    (headWindowPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  exact withSumPrimitive (Primrec.const true)
    (withSumPrimitive hlam (withSumPrimitive (Primrec.const true)
      (withSumPrimitive (Primrec.const true) (withSumPrimitive hord
        (withSumPrimitive hnum (withSumPrimitive (Primrec.const true) (Primrec.const true)))))))

theorem termGuardCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (tau : Ty) (code : Code (Fin n)) :
    (decide (tau ∈ S) && extraView n arity ((symbols, S), view code)) =
      NumberedUniverseRequests.guard arity symbols S (.term Gamma tau code) := by
  cases code <;> simp [extraView, withSum, view, NumberedUniverseRequests.guard]

theorem termGuardPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Window n × (List Ty × Ty × Code (Fin n)) =>
      NumberedUniverseRequests.guard arity p.1.1 p.1.2 (.term p.2.1 p.2.2.1 p.2.2.2)) := by
  have htype : Primrec (fun p : Window n × (List Ty × Ty × Code (Fin n)) =>
      decide (p.2.2.1 ∈ p.1.2)) :=
    ((memberPrimitive Ty).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst)).decide
  have h : Primrec (fun p : Window n × (List Ty × Ty × Code (Fin n)) =>
      decide (p.2.2.1 ∈ p.1.2) && extraView n arity (p.1, view p.2.2.2)) :=
    Primrec.and.comp htype
      ((extraViewPrimitive n arity).comp
        (Primrec.fst.pair ((NumberedCodeViewProof.viewPrimitive n).comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact h.of_eq (fun p => termGuardCalibration n arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

theorem guardPrimitive : NumberedUniverseGuardPrimrecTargets.ActualGuardPrimitive := by
  intro n arity
  have h : Primrec (withSum
      (fun p : Window n × (List Ty × Ty × Code (Fin n)) =>
        NumberedUniverseRequests.guard arity p.1.1 p.1.2 (.term p.2.1 p.2.2.1 p.2.2.2))
      (fun _ : Window n × (List Ty × List Ty × Code (Fin n)) => true)) :=
    withSumPrimitive (termGuardPrimitive n arity) (Primrec.const true)
  apply (h.comp (Primrec.fst.pair ((requestToPrimitive n).comp Primrec.snd))).of_eq
  intro p
  rcases p with ⟨⟨symbols, S⟩, request⟩
  cases request <;> rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecProof
