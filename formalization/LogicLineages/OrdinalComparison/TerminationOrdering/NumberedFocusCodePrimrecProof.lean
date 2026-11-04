module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecProof
open Source NumberedAuxiliaryCoding NumberedTypedFocus NumberedFocusCode
open NumberedFocusCodePrimrecSupportProof

attribute [local irreducible] Primrec

/-- Each successful descent pushes the original frame onto an inner-to-outer stack. -/
private def traceStep {Symbol : Type} (current : Option (Trace Symbol)) (position : Position) :
    Option (Trace Symbol) :=
  current.bind (fun result =>
    (descendCode position result.1).map (fun child =>
      (child, (position, result.1.2.2) :: result.2)))

private theorem traceFoldNone {Symbol : Type} (path : List Position) :
    path.foldl traceStep (none : Option (Trace Symbol)) = none := by
  induction path <;> simp_all [traceStep]

private theorem traceFoldCalibration {Symbol : Type} (path : List Position)
    (value : RawValue Symbol) (frames : List (Frame Symbol)) :
    path.foldl traceStep (some (value, frames)) =
      (traceCode path value).map (fun result => (result.1, result.2 ++ frames)) := by
  induction path generalizing value frames with
  | nil => simp [traceCode]
  | cons position path ih =>
    simp only [List.foldl_cons, traceStep, Option.bind_some]
    cases h : descendCode position value with
    | none => simp [h, traceCode, traceFoldNone]
    | some child =>
      simp only [Option.map_some]
      rw [ih]
      simp only [traceCode, h]
      cases hchild : traceCode path child <;> simp [hchild, List.append_assoc]

private theorem traceStepPrimitive (n : Nat) :
    Primrec (fun p : Option (Trace (Fin n)) × Position => traceStep p.1 p.2) := by
  let Input := Option (Trace (Fin n)) × Position
  have hdescend : Primrec (fun p : Input × Trace (Fin n) => descendCode p.1.2 p.2.1) :=
    (descendPrimitive n).comp ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have hresult : Primrec (fun p : (Input × Trace (Fin n)) × RawValue (Fin n) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hvalue := Primrec.fst.comp hresult
  have hcode := Primrec.snd.comp (Primrec.snd.comp hvalue)
  have hposition : Primrec (fun p : (Input × Trace (Fin n)) × RawValue (Fin n) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have houtput : Primrec (fun p : (Input × Trace (Fin n)) × RawValue (Fin n) =>
      (p.2, (p.1.1.2, p.1.2.1.2.2) :: p.1.2.2)) :=
    Primrec.snd.pair (Primrec.list_cons.comp (hposition.pair hcode) (Primrec.snd.comp hresult))
  have hmap : Primrec (fun p : Input × Trace (Fin n) =>
      (descendCode p.1.2 p.2.1).map (fun child => (child, (p.1.2, p.2.1.2.2) :: p.2.2))) :=
    Primrec.option_map hdescend houtput.to₂
  exact Primrec.option_bind Primrec.fst hmap.to₂

theorem tracePrimitive (n : Nat) :
    Primrec (fun p : List Position × RawValue (Fin n) => traceCode p.1 p.2) := by
  have hfold : Primrec (fun p : List Position × RawValue (Fin n) =>
      p.1.foldl traceStep (some (p.2, []))) :=
    Primrec.list_foldl Primrec.fst
      (Primrec.option_some.comp (Primrec.snd.pair (Primrec.const [])))
      ((traceStepPrimitive n).comp Primrec.snd).to₂
  apply hfold.of_eq
  rintro ⟨path, value⟩
  simpa using traceFoldCalibration path value []

theorem focusPrimitive : NumberedFocusCodeTargets.ActualFocusPrimitive := by
  intro n
  exact Primrec.option_map (tracePrimitive n) (Primrec.fst.comp Primrec.snd).to₂

theorem unwindPrimitive (n : Nat) :
    Primrec (fun p : List (Frame (Fin n)) × Code (Fin n) => unwindCode p.1 p.2) := by
  let Input := List (Frame (Fin n)) × Code (Fin n)
  have hstep : Primrec₂ (fun (_ : Input) (p : Option (Code (Fin n)) × Frame (Fin n)) =>
      p.1.bind (fun value => wrapCode p.2 value)) := by
    change Primrec (fun p : Input × (Option (Code (Fin n)) × Frame (Fin n)) =>
      p.2.1.bind (fun value => wrapCode p.2.2 value))
    exact Primrec.option_bind
      (f := fun p : Input × (Option (Code (Fin n)) × Frame (Fin n)) => p.2.1)
      (g := fun (p : Input × (Option (Code (Fin n)) × Frame (Fin n))) (value : Code (Fin n)) =>
        wrapCode p.2.2 value)
      (Primrec.fst.comp Primrec.snd)
      ((wrapPrimitive n).comp ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂
  exact Primrec.list_foldl Primrec.fst (Primrec.option_some.comp Primrec.snd) hstep

theorem replacementPrimitive : NumberedFocusCodeTargets.ActualReplacementPrimitive := by
  intro n
  let Input := (List Position × List Ty × Ty × Code (Fin n)) × Code (Fin n)
  have htrace : Primrec (fun p : Input => traceCode p.1.1 p.1.2) :=
    (tracePrimitive n).comp Primrec.fst
  have hunwind : Primrec (fun p : Input × Trace (Fin n) => unwindCode p.2.2 p.1.2) :=
    (unwindPrimitive n).comp ((Primrec.snd.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst))
  exact Primrec.option_bind htrace hunwind.to₂

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodePrimrecProof
