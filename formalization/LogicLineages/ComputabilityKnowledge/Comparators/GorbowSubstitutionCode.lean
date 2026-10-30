module

public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSubstitutionCode
open GorbowSyntax GorbowSyntaxValidation GorbowLiftedDictionary
open LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode

def ScannerInvariant : Prop :=
  (∀ (n m b : Nat) (σ : Fin n → Term m) (t : Term (n+b)) (tasks : List Task) (acc : List Nat),
    (GorbowTermPrefixCode.encode t).foldl (subStep n m (dictionary σ)) (some ((0,n+b)::tasks),acc) =
      (some tasks,acc ++ GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (liftN σ b) t))) ∧
  (∀ (n m b : Nat) (σ : Fin n → Term m) (φ : Formula (n+b)) (tasks : List Task) (acc : List Nat),
    (GorbowFormulaPrefixCode.encode φ).foldl (subStep n m (dictionary σ)) (some ((1,n+b)::tasks),acc) =
      (some tasks,acc ++ GorbowFormulaPrefixCode.encode (GorbowFormulaSubstitution.substituteFormula (liftN σ b) φ)))

def ExactOutput : Prop :=
  (∀ n m dict raw out, substituteTermCode n m dict raw = some out ↔
    ∃ (σ : Fin n → Term m) (t : Term n), dict = dictionary σ ∧ raw = GorbowTermPrefixCode.encode t ∧
      out = GorbowTermPrefixCode.encode (GorbowSubstitution.substitute σ t)) ∧
  (∀ n m dict raw out, substituteFormulaCode n m dict raw = some out ↔
    ∃ (σ : Fin n → Term m) (φ : Formula n), dict = dictionary σ ∧ raw = GorbowFormulaPrefixCode.encode φ ∧
      out = GorbowFormulaPrefixCode.encode (GorbowFormulaSubstitution.substituteFormula σ φ))

def ExactRejection : Prop :=
  (∀ n m dict raw, substituteTermCode n m dict raw = none ↔
    ¬ ∃ (σ : Fin n → Term m) (t : Term n), dict = dictionary σ ∧ raw = GorbowTermPrefixCode.encode t) ∧
  (∀ n m dict raw, substituteFormulaCode n m dict raw = none ↔
    ¬ ∃ (σ : Fin n → Term m) (φ : Formula n), dict = dictionary σ ∧ raw = GorbowFormulaPrefixCode.encode φ)

def Realization : Prop :=
  (∀ (n m : Nat) (σ : Fin n → Term m) (t : Term n) (I : Interpretation) (v : Fin m → Nat),
    ∃ out : Term m, substituteTermCode n m (dictionary σ) (GorbowTermPrefixCode.encode t) = some (GorbowTermPrefixCode.encode out) ∧
      out.realize I v = t.realize I (fun i => (σ i).realize I v)) ∧
  (∀ (n m : Nat) (σ : Fin n → Term m) (φ : Formula n) (I : Interpretation) (v : Fin m → Nat),
    ∃ out : Formula m, substituteFormulaCode n m (dictionary σ) (GorbowFormulaPrefixCode.encode φ) = some (GorbowFormulaPrefixCode.encode out) ∧
      (out.realize I v ↔ φ.realize I (fun i => (σ i).realize I v)))

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat × List (List Nat) × State × Nat => emit p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Nat × Nat × List (List Nat) × OutputState × Nat => subStep p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × List (List Nat) × List Nat => subRaw p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Nat × Nat × List (List Nat) × List Nat => substituteTermCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × List (List Nat) × List Nat => substituteFormulaCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := ScannerInvariant ∧ ExactOutput ∧ ExactRejection ∧ Realization ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSubstitutionCode
