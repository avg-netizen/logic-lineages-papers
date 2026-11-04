module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectionLeafPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCodePrimrecProof
open Source Source.SourceSpecialApplication NumberedAuxiliaryCoding NumberedExchangeCode NumberedSelfApplication
open NumberedSelfApplicationPrimrecProof NumberedSelectionLeafPrimrecProof
open NumberedDirectCodePrimrecProof

attribute [local irreducible] Primrec

abbrev Input (n : Nat) := List Ty × Nat × Ty × Code (Fin n)
abbrev RootInput (n : Nat) := Input n × NumberedCodeAssemblyPrimrecProof.NumberedData n

def rootSelfData (n : Nat) (p : RootInput n) : SelfData (Fin n) :=
  (p.2.1.pred,p.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2)

theorem rootSelfDataPrimitive (n : Nat) : Primrec (rootSelfData n) := by
  have h2 : Primrec (fun p : RootInput n => p.2.2) := Primrec.snd.comp Primrec.snd
  have h3 := Primrec.snd.comp h2
  have h4 := Primrec.snd.comp h3
  have h5 := Primrec.snd.comp h4
  exact (Primrec.pred.comp (Primrec.fst.comp Primrec.snd)).pair
    ((Primrec.fst.comp h2).pair ((Primrec.fst.comp h4).pair ((Primrec.fst.comp h5).pair (Primrec.snd.comp h5))))

def rootCopies (n : Nat) (p : RootInput n) : List (Entry n) := selfEntries (rootSelfData n p) p.1.1

theorem rootCopiesPrimitive (n : Nat) : Primrec (rootCopies n) :=
  (selfEntriesPrimitive n).comp ((rootSelfDataPrimitive n).pair (Primrec.fst.comp Primrec.fst))

def rootExpected (n : Nat) (p : RootInput n) : Ty := arrows p.1.1 p.1.2.2.1

theorem rootExpectedPrimitive (n : Nat) : Primrec (rootExpected n) :=
  arrowsPrimitive.comp ((Primrec.fst.comp Primrec.fst).pair
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))

def rootChoiceInput (n : Nat) (p : RootInput n × (List (Entry n) × List (Entry n))) : Choice n :=
  ((p.2.1++p.2.2,rootCopies n p.1),(p.1.1.2.1,rootExpected n p.1))

theorem rootChoiceInputPrimitive (n : Nat) : Primrec (rootChoiceInput n) :=
  ((Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).pair
    ((rootCopiesPrimitive n).comp Primrec.fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      ((rootExpectedPrimitive n).comp Primrec.fst))

def selectPayload (n : Nat) (p : RootInput n) : Option (Code (Fin n)) :=
  if p.2.1=0 then none else
    (bothEntries (p.2.2.2.2.1,p.2.2.2.2.2.2)).bind
      (fun entries => chooseResult (rootChoiceInput n (p,entries)))

theorem selectPayloadPrimitive (n : Nat) : Primrec (selectPayload n) := by
  have h4 : Primrec (fun p : RootInput n => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h5 := Primrec.snd.comp h4
  have hp := (bothEntriesPrimitive n).comp ((Primrec.fst.comp h4).pair (Primrec.snd.comp h5))
  have hc := (chooseResultPrimitive n).comp (rootChoiceInputPrimitive n)
  have h := Primrec.option_bind hp hc.to₂
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)) (Primrec.const none) h

theorem allSelectCodePrimitive : NumberedSelfApplicationTargets.ActualAllSelectCodePrimitive := by
  intro n
  have hn : Primrec (fun p : Input n => finiteNumberedParts p.2.2.2) :=
    (numberedPartsPrimitive n).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have h := Primrec.option_bind hn (selectPayloadPrimitive n).to₂
  apply h.of_eq
  rintro ⟨types,index,tau,code⟩
  cases code with
  | var i => rfl
  | lam sigma body => rfl
  | app sigma f a => rfl
  | bottom result => rfl
  | ordinary head base => rfl
  | argumentsNil => rfl
  | argumentsCons sigma q rest => rfl
  | numbered k head result base extraTypes extras =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [selectPayload,finiteNumberedParts,Option.bind_some,Nat.succ_ne_zero,if_false,Nat.pred_succ,
        bothEntries,chooseResult,rootChoiceInput,rootCopies,rootSelfData,rootExpected,selectCode,
        Option.bind_eq_bind,Option.map_eq_bind,Option.bind_assoc,Option.pure_def,Function.comp_def]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCodePrimrecProof
