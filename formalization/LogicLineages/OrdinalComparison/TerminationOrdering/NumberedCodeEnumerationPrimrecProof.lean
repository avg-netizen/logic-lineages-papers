module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration
open NumberedCodeEnumerationPrimrecSupportProof

/-- The two actual recursive calls at a successor, in prior/opened order. -/
def dependencies (bounds : Nat × Nat) : List (Nat × Nat) :=
  match bounds.2 with
  | 0 => []
  | fuel + 1 => [(bounds.1, fuel), (bounds.1 + 1, fuel)]

theorem dependenciesPrimitive : Primrec dependencies := by
  have h : Primrec (fun bounds : Nat × Nat =>
      (Nat.casesOn bounds.2 []
        (fun fuel => [(bounds.1, fuel), (bounds.1 + 1, fuel)]) : List (Nat × Nat))) :=
    Primrec.nat_casesOn Primrec.snd (Primrec.const [])
      (Primrec.list_cons.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
        (Primrec.list_cons.comp
          ((Primrec.succ.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
          (Primrec.const []))).to₂
  exact h.of_eq (by
    intro bounds
    unfold dependencies
    cases bounds.2 <;> rfl)

/-- Reconstruct the unchanged layer from the two recursive results. -/
def combine (n : Nat) (data : Parameters n)
    (p : (Nat × Nat) × List (List (Code (Fin n)))) : Option (List (Code (Fin n))) :=
  if p.1.2 = 0 then some [] else
    some (layer n (data, p.1.1, p.2.getD 0 [], p.2.getD 1 []))

theorem combinePrimitive (n : Nat) : Primrec₂ (combine n) := by
  have hvalues : Primrec (fun p : Parameters n × ((Nat × Nat) × List (List (Code (Fin n)))) =>
      p.2.2) := Primrec.snd.comp Primrec.snd
  have hprior : Primrec (fun p : Parameters n × ((Nat × Nat) × List (List (Code (Fin n)))) =>
      p.2.2.getD 0 []) :=
    (Primrec.list_getD ([] : List (Code (Fin n)))).comp hvalues (Primrec.const 0)
  have hopened : Primrec (fun p : Parameters n × ((Nat × Nat) × List (List (Code (Fin n)))) =>
      p.2.2.getD 1 []) :=
    (Primrec.list_getD ([] : List (Code (Fin n)))).comp hvalues (Primrec.const 1)
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 0))
    (Primrec.const (some []))
    (Primrec.option_some.comp ((layerPrimitive n).comp
      (Primrec.fst.pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
        (hprior.pair hopened)))))

theorem enumerationPrimitive : NumberedCodeEnumerationPrimrecTargets.ActualEnumerationPrimitive := by
  intro n
  apply Primrec.nat_omega_rec
    (m := fun (_ : Parameters n) (bounds : Nat × Nat) => bounds.2)
    (l := fun (_ : Parameters n) bounds => dependencies bounds)
    (g := combine n)
  · exact Primrec.snd.comp Primrec.snd
  · exact (dependenciesPrimitive.comp Primrec.snd).to₂
  · exact combinePrimitive n
  · intro data bounds child hchild
    rcases bounds with ⟨variableBound, fuel⟩
    cases fuel with
    | zero => simp [dependencies] at hchild
    | succ fuel =>
      simp only [dependencies, List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl <;> exact Nat.lt_succ_self fuel
  · intro data bounds
    rcases bounds with ⟨variableBound, fuel⟩
    cases fuel with
    | zero => rfl
    | succ fuel =>
      change some (layer n (data, variableBound,
        enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 variableBound fuel,
        enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 (variableBound + 1) fuel)) =
        some (enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 variableBound (fuel + 1))
      exact congrArg some (layerCalibration n data variableBound fuel)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeEnumerationPrimrecProof
