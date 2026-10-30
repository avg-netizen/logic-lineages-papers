module

public import LogicLineages.ComputabilityKnowledge.GorbowSelfApplicationCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelfApplicationCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowSelfApplicationCode

def ExactSelfApplication : Prop := ∀ raw out, selfApplicationCode raw = some out ↔
  ∃ φ : Formula 1, raw = GorbowFormulaPrefixCode.encode φ ∧ out = GorbowFormulaPrefixCode.encode (selfInstance φ)

def ExactRejection : Prop := ∀ raw,
  selfApplicationCode raw = none ↔ GorbowFormulaPrefixCode.decode 1 raw = none

def ExactSelectorApplication : Prop := ∀ raw out, selectorSelfApplicationCode raw = some out ↔
  ∃ A : Selector, raw = GorbowFormulaPrefixCode.encode A.val ∧ out = GorbowFormulaPrefixCode.encode (selfInstance A.val)

def StandardSemantics : Prop := ∀ (φ : Formula 1) (I : Interpretation),
  (selfInstance φ).realize I Fin.elim0 ↔
    φ.realize I (Fin.cases (GorbowCodeConstructors.formulaNumber φ) Fin.elim0)

def UniformPrograms : Prop := Primrec selfApplicationCode ∧ Primrec selectorSelfApplicationCode

def Target : Prop := ExactSelfApplication ∧ ExactRejection ∧ ExactSelectorApplication ∧ StandardSemantics ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelfApplicationCode
