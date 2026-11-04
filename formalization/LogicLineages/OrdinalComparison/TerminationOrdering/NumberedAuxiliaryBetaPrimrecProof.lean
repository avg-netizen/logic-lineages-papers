module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaPrimrecProof
open Source NumberedAuxiliaryCoding NumberedCodeView NumberedAuxiliarySubstitution
open NumberedHeadCodecPrimrecSupportProof NumberedAuxiliarySubstitutionPrimrecProof

attribute [local irreducible] substituteCode

def appParts {Symbol : Type} : Code Symbol → Option (Code Symbol × Code Symbol)
  | .app _ f a => some (f,a)
  | _ => none

def lamBody {Symbol : Type} : Code Symbol → Option (Code Symbol)
  | .lam _ body => some body
  | _ => none

def viewAppParts (n : Nat) : CodeView n → Option (Code (Fin n) × Code (Fin n)) :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none)
    (Sum.elim (fun p => some (p.2.1,p.2.2)) (fun _ => none)))

def viewLamBody (n : Nat) : CodeView n → Option (Code (Fin n)) :=
  Sum.elim (fun _ => none) (Sum.elim (fun p => some p.2) (fun _ => none))

theorem appPartsPrimitive (n : Nat) : Primrec (@appParts (Fin n)) := by
  have h : Primrec (viewAppParts n) := sumElim (Primrec.const none) (sumElim (Primrec.const none)
    (sumElim (Primrec.option_some.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)))
      (Primrec.const none)))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

theorem lamBodyPrimitive (n : Nat) : Primrec (@lamBody (Fin n)) := by
  have h : Primrec (viewLamBody n) := sumElim (Primrec.const none)
    (sumElim (Primrec.option_some.comp Primrec.snd) (Primrec.const none))
  exact (h.comp (NumberedCodeViewProof.viewPrimitive n)).of_eq (by intro code; cases code <;> rfl)

def betaEnvironment {Symbol : Type} (free : Nat) (a : Code Symbol) : List (Code Symbol) :=
  a :: (List.range free).map Code.var

theorem betaEnvironmentPrimitive (n : Nat) : Primrec₂ (@betaEnvironment (Fin n)) :=
  (Primrec.list_cons.comp Primrec.snd (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    ((NumberedCodeAssemblyPrimrecProof.varPrimitive n).comp Primrec.snd).to₂)).to₂

attribute [local irreducible] betaEnvironment

abbrev BetaContext (n : Nat) := (Nat × Code (Fin n)) × (Code (Fin n) × Code (Fin n))

theorem environmentArgumentsPrimitive (n : Nat) : Primrec (fun p : BetaContext n × Code (Fin n) =>
    betaEnvironment p.1.1.1 p.1.2.2) := by
  have hf : Primrec (fun p : BetaContext n × Code (Fin n) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : BetaContext n × Code (Fin n) => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact (betaEnvironmentPrimitive n).comp hf ha

theorem substitutionBinaryPrimitive (n : Nat) : Primrec₂ (@substituteCode (Fin n)) :=
  (codeSubstitutionPrimitive n).to₂

theorem substituteBodyPrimitive (n : Nat) : Primrec (fun p : BetaContext n × Code (Fin n) =>
    substituteCode (betaEnvironment p.1.1.1 p.1.2.2) p.2) :=
  (substitutionBinaryPrimitive n).comp (environmentArgumentsPrimitive n) Primrec.snd

theorem allBetaCodePrimitive : NumberedAuxiliarySubstitutionTargets.ActualAllBetaCodePrimitive := by
  intro n
  have hm : Primrec (fun p : BetaContext n × Code (Fin n) =>
      substituteCode (betaEnvironment p.1.1.1 p.1.2.2) p.2) :=
    substituteBodyPrimitive n
  have hi : Primrec (fun p : BetaContext n =>
      (lamBody p.2.1).map (fun body => substituteCode (betaEnvironment p.1.1 p.2.2) body)) :=
    Primrec.option_map ((lamBodyPrimitive n).comp (Primrec.fst.comp Primrec.snd)) hm.to₂
  have h := Primrec.option_bind ((appPartsPrimitive n).comp Primrec.snd) hi.to₂
  have hc : Primrec (fun p : Nat × Code (Fin n) => betaCode p.1 p.2) := by
    apply h.of_eq
    rintro ⟨free,code⟩
    cases code with
    | app sigma f a => cases f <;> simp only [betaEnvironment] <;> rfl
    | var index => rfl
    | lam sigma body => rfl
    | bottom tau => rfl
    | ordinary head base => rfl
    | numbered k head tau base types extras => rfl
    | argumentsNil => rfl
    | argumentsCons sigma q rest => rfl
  exact hc.to₂

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaPrimrecProof
