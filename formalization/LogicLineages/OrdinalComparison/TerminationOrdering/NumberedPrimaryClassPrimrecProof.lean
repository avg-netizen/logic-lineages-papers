module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecProof
open Source NumberedRewriteReduction NumberedAuxiliaryDecoding NumberedExchangeNeighborhood
open NumberedPrimaryClassPrimrec

local instance {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {Gamma : List Ty} : DecidableEq (Packed Symbol arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

private abbrev SeedInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma

private abbrev StepInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (List (Fin n) × List Ty) ×
    List (Packed (Fin n) arity Gamma) × List (Packed (Fin n) arity Gamma)

private abbrev RunInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  SeedInput n arity Gamma × Nat

private abbrev TestInput (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :=
  (List (Fin n) × List Ty) ×
    Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma

private theorem anyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) := by
  have hfold : Primrec (fun a => (f a).foldr (fun b rest => g a b || rest) false) :=
    Primrec.list_foldr hf (Primrec.const false)
      (Primrec.or.comp
        (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  apply hfold.of_eq
  intro a
  induction f a <;> simp_all

private theorem filterPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).filter (g a)) := by
  have hchoice : Primrec (fun p : A × B =>
      bif g p.1 p.2 then some p.2 else none) :=
    Primrec.cond hg (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have hfilter : Primrec (fun a => (f a).filterMap
      (fun b => bif g a b then some b else none)) :=
    Primrec.listFilterMap hf hchoice.to₂
  apply hfilter.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b rest ih =>
    cases hb : g a b <;> simp [hb, ih]

theorem reachableListCalibration : NumberedPrimaryClassPrimrecTargets.ActualReachableListCalibration :=
  NumberedPrimaryClassPrimrecSupportProof.reachableListCalibration

theorem primaryListCalibration : NumberedPrimaryClassPrimrecTargets.ActualPrimaryListCalibration :=
  NumberedPrimaryClassPrimrecSupportProof.primaryListCalibration

theorem vertexListPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma =>
      vertexList p.1.1 p.1.2 p.2) :=
  Primrec.list_cons.comp Primrec.snd
    (NumberedClassCandidatesPrimrecProof.classCandidatesPrimitive n arity Gamma)

theorem stepPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : (List (Fin n) × List Ty) ×
        List (Packed (Fin n) arity Gamma) × List (Packed (Fin n) arity Gamma) =>
      step p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hedge : Primrec (fun p :
      (StepInput n arity Gamma × Packed (Fin n) arity Gamma) × Packed (Fin n) arity Gamma =>
      exchangeTest p.1.1.1.1 p.1.1.1.2 p.2 p.1.2) :=
    (NumberedExchangePrimrecProof.exchangeTestPrimitive n arity Gamma).comp
      (g := fun p :
        (StepInput n arity Gamma × Packed (Fin n) arity Gamma) × Packed (Fin n) arity Gamma =>
        (p.1.1.1, p.2, p.1.2))
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))
  have hadjacent : Primrec (fun p : StepInput n arity Gamma × Packed (Fin n) arity Gamma =>
      p.1.2.2.any (fun a => exchangeTest p.1.1.1 p.1.1.2 a p.2)) :=
    anyPrimitive
      (f := fun p : StepInput n arity Gamma × Packed (Fin n) arity Gamma => p.1.2.2)
      (g := fun (p : StepInput n arity Gamma × Packed (Fin n) arity Gamma)
        (a : Packed (Fin n) arity Gamma) => exchangeTest p.1.1.1 p.1.1.2 a p.2)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hedge.to₂
  have hfilter : Primrec (fun p : StepInput n arity Gamma =>
      p.2.1.filter (fun r => p.2.2.any (fun a => exchangeTest p.1.1 p.1.2 a r))) :=
    filterPrimitive
      (f := fun p : StepInput n arity Gamma => p.2.1)
      (g := fun (p : StepInput n arity Gamma) (r : Packed (Fin n) arity Gamma) =>
        p.2.2.any (fun a => exchangeTest p.1.1 p.1.2 a r))
      (Primrec.fst.comp Primrec.snd) hadjacent.to₂
  exact (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) hfilter).of_eq
    (by intro p; rfl)

private theorem seedStepPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : SeedInput n arity Gamma × List (Packed (Fin n) arity Gamma) =>
      step p.1.1.1 p.1.1.2 (vertexList p.1.1.1 p.1.1.2 p.1.2) p.2) :=
  (stepPrimitive n arity Gamma).comp
    (g := fun p : SeedInput n arity Gamma × List (Packed (Fin n) arity Gamma) =>
      (p.1.1, vertexList p.1.1.1 p.1.1.2 p.1.2, p.2))
    ((Primrec.fst.comp Primrec.fst).pair
      (((vertexListPrimitive n arity Gamma).comp Primrec.fst).pair Primrec.snd))

theorem reachableListPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : ((List (Fin n) × List Ty) × Packed (Fin n) arity Gamma) × Nat =>
      reachableList p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold reachableList
  exact Primrec.nat_iterate
    (f := fun p : RunInput n arity Gamma => p.2)
    (g := fun p : RunInput n arity Gamma => [p.1.2])
    (h := fun (p : RunInput n arity Gamma) (reached : List (Packed (Fin n) arity Gamma)) =>
      step p.1.1.1 p.1.1.2 (vertexList p.1.1.1 p.1.1.2 p.1.2) reached)
    Primrec.snd
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) (Primrec.const []))
    ((seedStepPrimitive n arity Gamma).comp
      (g := fun p : RunInput n arity Gamma × List (Packed (Fin n) arity Gamma) =>
        (p.1.1, p.2))
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem primaryListPrimitive : NumberedPrimaryClassPrimrecTargets.ActualPrimaryListPrimitive := by
  intro n arity Gamma
  exact ((reachableListPrimitive n arity Gamma).comp
    (g := fun p : SeedInput n arity Gamma => (p, (vertexList p.1.1 p.1.2 p.2).length))
    (Primrec.id.pair (Primrec.list_length.comp (vertexListPrimitive n arity Gamma)))).of_eq
    (by intro p; rfl)

theorem primaryTestPrimitive : NumberedPrimaryClassPrimrecTargets.ActualPrimaryTestPrimitive := by
  intro n arity Gamma
  have hclass : Primrec (fun p : TestInput n arity Gamma =>
      primaryList p.1.1 p.1.2 p.2.1) :=
    (primaryListPrimitive n arity Gamma).comp
      (g := fun p : TestInput n arity Gamma => (p.1, p.2.1))
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have htest : Primrec (fun p : TestInput n arity Gamma =>
      decide (p.2.2 ∈ primaryList p.1.1 p.1.2 p.2.1)) :=
    (NumberedHeadWindowPrimrecProof.memberPrimitive (Packed (Fin n) arity Gamma)).decide.comp
      (Primrec.snd.comp Primrec.snd) hclass
  exact htest.of_eq (fun p : TestInput n arity Gamma =>
    NumberedPrimaryClassPrimrecSupportProof.primaryTestCalibration p.1.1 p.1.2 p.2.1 p.2.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryClassPrimrecProof
