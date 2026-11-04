module

public import LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplicationDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions

@[expose] public section
/-! One retained-parameter common-knowledge formula, with the actual source
registry program for two-variable substitution. The fixed-point clauses below
are literal closed instances in the constructed D, not an asserted internally
quantified CBE theorem or a family of unrelated closed diagonal sentences. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge
open GorbowSyntax GorbowPRProgram GorbowSortedSyntaxCode List.Vector

/-- Context beneath each displayed universal is [agent,self-code,parameter]. -/
def template (tag : Nat) (A : Selector) : Formula 2 :=
  .conj
    (.all (.imp (.agent (.var 0))
      (.imp (GorbowFormulaSubstitution.substituteFormula
        (fun _ : Fin 1 => (.var 0 : Term 3)) A.val)
        (.knowledge (.var 0) (.var 2)))))
    (.all (.imp (.agent (.var 0))
      (.imp (GorbowFormulaSubstitution.substituteFormula
        (fun _ : Fin 1 => (.var 0 : Term 3)) A.val)
        (.knowledge (.var 0) (GorbowPRDefiningEquations.call tag
          (.var 1 ::ᵥ .var 2 ::ᵥ nil))))))

/-- This is ONE Formula 1 for the selector, for every sentence parameter. -/
def common (tag : Nat) (A : Selector) : Formula 1 :=
  GorbowParameterSelfApplication.openSelf (template tag A)

def closedInstance (tag : Nat) (A : Selector) (sigma : Sentence) : Sentence :=
  GorbowStandardInstances.instantiate (common tag A) (Term.numeral (formulaCode sigma))

/-- A unary formula to which Hilbert equality substitution can literally apply. -/
def literalBody (A : Selector) (sigma : Sentence) : Formula 1 :=
  .conj
    (GorbowTheoryProof.weakenClosed 1 (everyone A (formulaCode sigma)))
    (.all (.imp (.agent (.var 0))
      (.imp (GorbowFormulaSubstitution.substituteFormula
        (fun _ : Fin 1 => (.var 0 : Term 2)) A.val)
        (.knowledge (.var 0) (.var 1)))))

def closedCall (tag : Nat) (A : Selector) (sigma : Sentence) : Term 0 :=
  GorbowPRDefiningEquations.call tag
    (Term.numeral (formulaCode (template tag A)) ::ᵥ
      Term.numeral (formulaCode sigma) ::ᵥ nil)

def CodeProgram (p : Program 2) : Prop :=
  ∀ code u, evaluate p (code ::ᵥ u ::ᵥ nil) =
    (GorbowParameterSelfApplication.numeric code u).getD 0

def RegistryInstall (pF pR : Program 1) (q : Program 5)
    (tag : Nat) (p : Program 2) : Prop :=
  (GorbowPRRegistry.nodes (GorbowSourceRegistryPadding.root
    (GorbowPublishedDCB.augmented pF q) pR))[tag]? = some ⟨2, p⟩

def FixedPointFor (pF pR : Program 1) (q : Program 5)
    (c : Nat.Partrec.Code) (tag : Nat) : Prop :=
  ∀ (A : Selector) (sigma : Sentence),
    Nonempty (GorbowTheoryProof.Derivation (GorbowPublishedDCB.D pF pR q c)
      (GorbowBooleanTruth.biconditional (closedInstance tag A sigma)
        (.conj (everyone A (formulaCode sigma))
          (everyone A (formulaCode (closedInstance tag A sigma))))))

end LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge
