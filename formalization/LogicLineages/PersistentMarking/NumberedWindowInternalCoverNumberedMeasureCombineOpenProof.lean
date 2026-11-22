module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureMaximumProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalArithmeticProgramsSupportProof (additionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalChosenAuxMeasureCombine
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open ID1Completion.InternalUnpairArithmeticProof (leftWeakAdd)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (rightWeakAdd weakTrans)
open NumberedWindowInternalCoverNumberedMeasureMaximumProof (exact_OpenCoverMaximumWeak)
open NumberedWindowInternalCoverNumberedMeasureCombineTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem oneGraph {n : Nat} (p : Program 1) (q : Program n) (out val : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p out ![val])))
    (hq : Nonempty (Derivation body Γ (programGraph q val xs))) :
    Nonempty (Derivation body Γ (programGraph (callOne p q) out xs)) := by
  apply compositionValue p (fun _ : Fin 1 => q) out xs ![val] hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact hq

private theorem selectors {n : Nat} (a b : Program n) (x y : OTerm α) (xs : Fin n → OTerm α)
    (ha : Nonempty (Derivation body Γ (programGraph a x xs)))
    (hb : Nonempty (Derivation body Γ (programGraph b y xs))) (i : Fin 2) :
    Nonempty (Derivation body Γ (programGraph ((![a,b] : Fin 2 → Program n) i) ((![x,y] : Fin 2 → OTerm α) i) xs)) :=
  Fin.cases ha (Fin.cases hb (fun j => Fin.elim0 j)) i

private theorem twoGraph {n : Nat} (p : Program 2) (a b : Program n) (out x y : OTerm α)
    (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph p out ![x,y])))
    (ha : Nonempty (Derivation body Γ (programGraph a x xs)))
    (hb : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (callTwo p a b) out xs)) :=
  compositionValue p ![a,b] out xs ![x,y] hp (selectors a b x y xs ha hb)

private theorem field (p : Program 1) (i : Fin 2) (v : OTerm α) (xs : Fin 2 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph p v ![xs i]))) :
    Nonempty (Derivation body Γ (programGraph (coordinate p i) v xs)) :=
  oneGraph p (.projection i) v (xs i) xs h (projectionValue i xs)

private theorem liftTail (P : Program 2) (o k l r : OTerm α)
    (report : Nonempty (Derivation body Γ (programGraph P o ![l,r]))) :
    Nonempty (Derivation body Γ (programGraph (reorder P ![1,2]) o ![k,l,r])) := by
  let xs : Fin 3 → OTerm α := ![k,l,r]
  apply compositionValue P (fun i : Fin 2 => Program.projection ((![1,2] : Fin 2 → Fin 3) i))
    o xs ![l,r] report
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs) (fun j => Fin.elim0 j)) i

theorem exact_OpenCoverNumberedJoin : ExactOpenCoverNumberedJoin := by
  intro body α Γ p k ml mr dl dr wl wr mid width mlCode mrCode midGraph widthGraph out
  let L := ID1Completion.InternalUnpair.left
  let R := ID1Completion.InternalUnpair.right
  let xs : Fin 2 → OTerm α := ![ml,mr]
  let ys : Fin 3 → OTerm α := ![k,ml,mr]
  obtain ⟨invL⟩ := actualOriginalGeneratedCodeInverse body α ml dl wl
  obtain ⟨invR⟩ := actualOriginalGeneratedCodeInverse body α mr dr wr
  obtain ⟨mlPaid⟩ := mlCode
  obtain ⟨mrPaid⟩ := mrCode
  have fieldsL := Derivation.implicationElimination (weakenClosed invL Γ) mlPaid
  have fieldsR := Derivation.implicationElimination (weakenClosed invR Γ) mrPaid
  have sum : Nonempty (Derivation body Γ (programGraph predecessorDepth (add dl dr) xs)) :=
    twoGraph ID1Completion.InternalArithmeticPrograms.addition (coordinate L 0) (coordinate L 1)
      (add dl dr) dl dr xs (additionValue dl dr)
      (field L 0 dl xs ⟨Derivation.conjunctionLeft fieldsL⟩)
      (field L 1 dr xs ⟨Derivation.conjunctionLeft fieldsR⟩)
  have trueDepth : Nonempty (Derivation body Γ (programGraph numberedPredDepth (add dl dr) ys)) :=
    liftTail predecessorDepth (add dl dr) k ml mr sum
  have depth := oneGraph .succ numberedPredDepth (suc (add dl dr)) (add dl dr) ys
    (successorValue ![add dl dr]) trueDepth
  have inner : Nonempty (Derivation body Γ (programGraph numeralBound mid xs)) :=
    twoGraph maximum (coordinate R 0) (coordinate R 1) mid wl wr xs midGraph
      (field R 0 wl xs ⟨Derivation.conjunctionRight fieldsL⟩)
      (field R 1 wr xs ⟨Derivation.conjunctionRight fieldsR⟩)
  have children : Nonempty (Derivation body Γ (programGraph numberedChildMax mid ys)) :=
    liftTail numeralBound mid k ml mr inner
  have maxWidth : Nonempty (Derivation body Γ (programGraph numberedWidth width ys)) :=
    twoGraph maximum (.projection 0) numberedChildMax width k mid ys widthGraph (projectionValue 0 ys) children
  have terminal := compositionRecover ID1Completion.InternalPairing.pairing
    ![callOne .succ numberedPredDepth,numberedWidth] p ys ![suc (add dl dr),width] out
    (selectors (callOne .succ numberedPredDepth) numberedWidth (suc (add dl dr)) width ys depth maxWidth)
  obtain ⟨bothChild⟩ := exact_OpenCoverMaximumWeak body α Γ wl wr mid midGraph
  obtain ⟨finalWeights⟩ := exact_OpenCoverMaximumWeak body α Γ k mid width widthGraph
  exact ⟨terminal,leftWeakAdd dl dr,rightWeakAdd dl dr,
    weakTrans wl mid width ⟨Derivation.conjunctionLeft bothChild⟩ ⟨Derivation.conjunctionRight finalWeights⟩,
    weakTrans wr mid width ⟨Derivation.conjunctionRight bothChild⟩ ⟨Derivation.conjunctionRight finalWeights⟩,
    ⟨Derivation.conjunctionLeft finalWeights⟩⟩

#print axioms exact_OpenCoverNumberedJoin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineOpenProof
