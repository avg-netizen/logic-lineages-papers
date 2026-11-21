module
public import LogicLineages.PermittedControl.PreparedStripReconstructionTargets
import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryEffectiveProof
import LogicLineages.PermittedControl.FiniteStripRecoveryFoldProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedStripReconstruction
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection FiniteStripRecovery FiniteStripCollectorRecovery

private theorem collectArgsComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (fun q : StripCodeArgs => collectCode f q.1 q.2.1 q.2.2.1) := by
  have hx : Computable (@Prod.fst Nat (Nat × List NamedCode × Nat)) :=
    Computable.fst
  have hrest : Computable (@Prod.snd Nat (Nat × List NamedCode × Nat)) :=
    Computable.snd
  have ha' : Computable (@Prod.fst Nat (List NamedCode × Nat)) :=
    Computable.fst
  have hrs' : Computable (@Prod.snd Nat (List NamedCode × Nat)) :=
    Computable.snd
  have hfirst : Computable (@Prod.fst (List NamedCode) Nat) :=
    Computable.fst
  have ha : Computable (fun q : StripCodeArgs => q.2.1) :=
    Computable.comp ha' hrest
  have htail : Computable (fun q : StripCodeArgs => q.2.2) :=
    Computable.comp hrs' hrest
  have hrs : Computable (fun q : StripCodeArgs => q.2.2.1) :=
    Computable.comp hfirst htail
  have hxa : Computable (fun q : StripCodeArgs => (q.1,q.2.1)) :=
    Computable.pair hx ha
  have hpack : Computable (fun q : StripCodeArgs => ((q.1,q.2.1),q.2.2.1)) :=
    Computable.pair hxa hrs
  have hcol₂ : Computable₂ (fun p : Nat × Nat => collectCode f p.1 p.2) :=
    (collectorEffective f hf).2
  have hcol : Computable (fun p : (Nat × Nat) × List NamedCode =>
      collectCode f p.1.1 p.1.2 p.2) := hcol₂
  exact Computable.comp
    (f := fun p : (Nat × Nat) × List NamedCode => collectCode f p.1.1 p.1.2 p.2)
    (g := fun q : StripCodeArgs => ((q.1,q.2.1),q.2.2.1)) hcol hpack

private theorem foldResultComputable :
    Computable₂ (fun (q : StripCodeArgs) (r : Option (List (Nat × Nat))) =>
      r.map (fun reads => foldCode reads q.2.2.2)) := by
  let A := StripCodeArgs × Option (List (Nat × Nat))
  have hcode : Computable (fun p : A × List (Nat × Nat) => p.1.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.fst.comp Computable.fst)))
  have hfold : Computable₂ (fun (p : A) (reads : List (Nat × Nat)) =>
      foldCode reads p.1.2.2.2) :=
    foldCodeExact.1.to_comp.comp Computable.snd hcode
  exact Computable.option_map Computable.snd hfold

private theorem specializeComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (specializeCode f) :=
  Computable.option_map (collectArgsComputable f hf) foldResultComputable

private theorem constantCheckPrimitive : Primrec constantCheck := by
  have htest := ClosedLinearStatementChecks.actual_numeric_programs.1
  have heval := ClosedLinearStatementChecks.actual_numeric_programs.2.1
  have hguard : PrimrecPred (fun code : Nat => ClosedLinear.Code.constantMatrix code = true) :=
    Primrec.eq.comp htest (Primrec.const true)
  exact Primrec.ite hguard (Primrec.option_some.comp heval) (Primrec.const none)

private theorem checkComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (checkStripCode f) :=
  (Primrec.option_map₁ (Primrec.option_map₁ constantCheckPrimitive)).to_comp.comp
    (specializeComputable f hf)

theorem codeExact : CodeExact := by
  refine ⟨fun f hf => ⟨specializeComputable f hf,checkComputable f hf⟩,?_,?_⟩
  · intro f x a rs code
    constructor
    · intro h
      change (collectCode f x a rs).map (fun r => r.map (fun reads => foldCode reads code)) = none
      rw [h] <;> rfl
    · intro h
      change (collectCode f x a rs).map (fun r => r.map (fun reads => foldCode reads code)) = some none
      rw [h] <;> rfl
  · intro f x a rs reads p h
    change (collectCode f x a rs).map (fun r => r.map (fun vals => foldCode vals p.encode)) =
      some (some (foldFormula reads p).encode)
    rw [h]
    exact congrArg (fun c => some (some c)) (foldCodeExact.2 reads p)

end LogicLineages.PermittedControl.PreparedStripReconstruction
