module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadPrimitiveProof
import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseCodeProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldEffectiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
open OrdinalComparison FieldComparison

private theorem coreComputable (f : Nat → Nat) (hf : Computable f) : Computable (readCore f) := by
  have left : Primrec (fun p : Args => (payload p).1) := Primrec.fst.comp payloadPrimitive
  have right : Primrec (fun p : Args => (payload p).2) := Primrec.snd.comp payloadPrimitive
  have aff : Computable (fun p : Args => packAffine (signedBank p)) :=
    (packAffinePrimitive.comp signedBankPrimitive).to_comp
  have collapse : Computable (fun p : Args => packBase
      (ArbitraryFixedHeadCollapse.read f ((payload p).1,inputValue p))) :=
    packBasePrimitive.to_comp.comp ((ArbitraryFixedHeadCollapse.effectivity.2 f hf).comp
      (left.pair inputPrimitive).to_comp)
  have someValue := (closedOrdinaryFieldEffective f hf).2.1
  have someCount := (closedOrdinaryFieldEffective f hf).2.2
  have iterInput : Primrec (fun p : Args => ((0,(payload p).1,0,0) : LongFieldCode)) :=
    (Primrec.const 0).pair (left.pair (Primrec.const (0,0)))
  have entryInput : Primrec (fun p : Args => ((1,0,(payload p).1,(payload p).2) : LongFieldCode)) :=
    (Primrec.const 1).pair ((Primrec.const 0).pair payloadPrimitive)
  have it : Computable (fun p : Args => packField
      (closedOrdinaryValueField f (0,(payload p).1,0,0) (inputValue p))) :=
    packFieldPrimitive.to_comp.comp (someValue.comp iterInput.to_comp inputPrimitive.to_comp)
  have entry : Computable (fun p : Args => packField
      (closedOrdinaryValueField f (1,0,(payload p).1,(payload p).2) (inputValue p))) :=
    packFieldPrimitive.to_comp.comp (someValue.comp entryInput.to_comp inputPrimitive.to_comp)
  have count : Computable (fun p : Args => packField
      (closedOrdinaryCountField f ((payload p).1,(payload p).2,inputValue p))) :=
    packFieldPrimitive.to_comp.comp (someCount.comp (left.pair (right.pair inputPrimitive)).to_comp)
  have iEntry : Computable (fun p : Args => identityValueCode ((payload p).1,inputValue p,inputValue p)) :=
    (identityValueCodePrimitive.comp (left.pair (inputPrimitive.pair inputPrimitive))).to_comp
  have iCount : Computable (fun p : Args => identityValueCode ((payload p).1,inputValue p,0)) :=
    (identityValueCodePrimitive.comp (left.pair (inputPrimitive.pair (Primrec.const 0)))).to_comp
  apply (Computable.cond (sameTag 0).to_comp aff
    (Computable.cond (sameTag 1).to_comp collapse
      (Computable.cond (sameTag 2).to_comp it
        (Computable.cond (sameTag 3).to_comp entry
          (Computable.cond (sameTag 4).to_comp count
            (Computable.cond (sameTag 5).to_comp iEntry iCount)))))).of_eq
  intro p
  by_cases h0 : tag p = 0
  · simp [readCore,h0]
  by_cases h1 : tag p = 1
  · simp [readCore,h0,h1]
  by_cases h2 : tag p = 2
  · simp [readCore,h0,h1,h2]
  by_cases h3 : tag p = 3
  · simp [readCore,h0,h1,h2,h3]
  by_cases h4 : tag p = 4
  · simp [readCore,h0,h1,h2,h3,h4]
  by_cases h5 : tag p = 5
  · simp [readCore,h0,h1,h2,h3,h4,h5]
  · simp [readCore,h0,h1,h2,h3,h4,h5]

theorem readComputable (f : Nat → Nat) (hf : Computable f) : Computable (readCode f) :=
  (Computable.cond parserPrimitive.to_comp (coreComputable f hf) (Computable.const 0)).of_eq
    (fun p => by cases h : parser p <;> simp [readCode,h])

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
