module

public import LogicLineages.ComputabilityKnowledge.GorbowSelectedCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelectedCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowSelectedCode

def LiteralCalibration : Prop := ∀ A σ,
  everyoneRaw (GorbowFormulaPrefixCode.encode A.val) (GorbowFormulaPrefixCode.encode σ) =
    GorbowFormulaPrefixCode.encode (everyoneSentence A σ)

def ExactEveryone : Prop := ∀ a s out, everyoneCode a s = some out ↔
  ∃ (A : Selector) (σ : Sentence), a = GorbowFormulaPrefixCode.encode A.val ∧
    s = GorbowFormulaPrefixCode.encode σ ∧ out = GorbowFormulaPrefixCode.encode (everyoneSentence A σ)

def ExactNonempty : Prop := ∀ a out, nonemptyCode a = some out ↔
  ∃ A : Selector, a = GorbowFormulaPrefixCode.encode A.val ∧
    out = GorbowFormulaPrefixCode.encode (selectedNonempty A)

def ExactTheta : Prop := ∀ a out, thetaCode a = some out ↔
  ∃ A : Selector, a = GorbowFormulaPrefixCode.encode A.val ∧ out = GorbowFormulaPrefixCode.encode (theta A)

def Realization : Prop := ∀ (I : Interpretation) (A : Selector) (σ : Sentence),
  ((everyoneSentence A σ).realize I Fin.elim0 ↔
    ∀ x, I.agents x → A.val.realize I (Fin.cases x Fin.elim0) → I.knowledge x (GorbowCodeConstructors.formulaNumber σ)) ∧
  ((selectedNonempty A).realize I Fin.elim0 ↔ ∃ x, I.agents x ∧ A.val.realize I (Fin.cases x Fin.elim0)) ∧
  ((theta A).realize I Fin.elim0 ↔ ¬ (everyoneSentence A falseEquality).realize I Fin.elim0)

def UniformPrograms : Prop :=
  Primrec (fun p : List Nat × List Nat => everyoneRaw p.1 p.2) ∧
  Primrec (fun p : List Nat × List Nat => everyoneCode p.1 p.2) ∧
  Primrec nonemptyCode ∧ Primrec thetaCode

def Target : Prop := LiteralCalibration ∧ ExactEveryone ∧ ExactNonempty ∧ ExactTheta ∧ Realization ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelectedCode
