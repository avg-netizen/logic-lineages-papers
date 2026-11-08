module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericQuotientEdgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeChecker
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The source uses the original universe decoder, including its literal
window filter. The default is relevant only when the step checker rejects. -/
def sourceRepresentativeValue (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) : Nat :=
  match NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma value with
  | none => 0
  | some q => NumberedLeastCodeRepresentative.representativeCode symbols S q

/-- The original edge checker decodes its target as a packed term, without
an additional universe filter. This distinction is retained for every S. -/
def targetRepresentativeValue (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) : Nat :=
  match NumberedNumericDecoding.decodePackedNumber n arity Gamma value with
  | none => 0
  | some q => NumberedLeastCodeRepresentative.representativeCode symbols S q

structure Data where
  stepProgram : Program 3
  sourceRepresentative : Program 1
  targetRepresentative : Program 1

/-- A fixed original finite window and ambient context. Every calibration
quantifies all natural inputs; no subtype closure or successful decode is assumed. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  (∀ v : List.Vector Nat 3, evaluate data.stepProgram v =
    (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2)).toNat) ∧
  (∀ v : List.Vector Nat 1, evaluate data.sourceRepresentative v =
    sourceRepresentativeValue n arity symbols S Gamma (v.get 0)) ∧
  (∀ v : List.Vector Nat 1, evaluate data.targetRepresentative v =
    targetRepresentativeValue n arity symbols S Gamma (v.get 0))

/-- All checker nodes read [source endpoint, target endpoint, certificate]. -/
def field (selector : Program 1) : Program 3 :=
  .composition selector (fun _ : Fin 1 => .projection 2)

def stepAt (data : Data) : Program 3 :=
  .composition data.stepProgram ![field source,field target,field step]

def representativeAt (representative selector : Program 1) : Program 3 :=
  .composition representative (fun _ : Fin 1 => field selector)

def representativeCheck (representative selector : Program 1) (endpoint : Fin 3) : Program 3 :=
  .composition InternalEqualityTest.equalityTest
    ![representativeAt representative selector,.projection endpoint]

/-- An explicit original-Program AST. The successful step already ensures
both original decoders succeeded; the other two conjuncts compare their
actual representative outputs with the supplied endpoints. -/
def checker (data : Data) : Program 3 :=
  InternalAcceptance.conjunction (stepAt data)
    (InternalAcceptance.conjunction
      (representativeCheck data.sourceRepresentative source 0)
      (representativeCheck data.targetRepresentative target 1))

def accepted {α : Type} (data : Data) (x y certificate : OTerm α) : Formula α :=
  graph3 (checker data) (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) x y certificate

def requirements {α : Type} (data : Data) (x y rawSource rawTarget rawStep : OTerm α) : Formula α :=
  graph3 data.stepProgram (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    rawSource rawTarget rawStep ⊓
      (graph1 data.sourceRepresentative x rawSource ⊓ graph1 data.targetRepresentative y rawTarget)

/-- Supplied values are genuine original graph witnesses, not semantic
evaluation equations used as new axioms of the internal calculus. -/
def valuePremises {α : Type} (data : Data)
    (certificate rawSource rawTarget rawStep sourceValue targetValue : OTerm α) : Formula α :=
  selectors certificate rawSource rawTarget rawStep ⊓
    (graph1 data.sourceRepresentative sourceValue rawSource ⊓
      graph1 data.targetRepresentative targetValue rawTarget)

def valueRequirements {α : Type} (data : Data)
    (x y rawSource rawTarget rawStep sourceValue targetValue : OTerm α) : Formula α :=
  graph3 data.stepProgram (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    rawSource rawTarget rawStep ⊓ (equal sourceValue x ⊓ equal targetValue y)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeChecker
