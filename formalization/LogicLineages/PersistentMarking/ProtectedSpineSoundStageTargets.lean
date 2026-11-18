import LogicLineages.PersistentMarking.ProtectedSpineSoundRelation
import LogicLineages.PersistentMarking.MarkedConstructorOperator

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundStageTargets
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation

inductive BaseRelated (F : Inputs S) (Γ : Context) : List MarkedExtras.Tagged → Args → Prop where
  | nil : BaseRelated F Γ [] .nil
  | cons : Related F q.type Γ c (some q) → BaseRelated F Γ cs qs →
      BaseRelated F Γ ((q.type,c)::cs) (.cons q qs)

def ExtrasRelated (F : Inputs S) (Γ : Context) (es : Args) (xs : List MarkedExtras.Tagged) : Prop :=
  ∀ a, a ∈ xs → ∃ i q, At es i q ∧ a.1 = q.type ∧ Related F a.1 Γ a.2 (some q)

def OwnerRelated (F : Inputs S) (p : MarkedFamilyParameters.Parameter) (bs es : Args) : Prop :=
  MarkedFamilyParameters.Valid (domain F) F.data.sourceHeads p ∧
  PaperTerm S (.marked p.1 p.2.1 bs es) p.2.1 ∧
  Source F p.2.2.1 (.marked p.1 p.2.1 bs es) ∧
  BaseRelated F p.2.2.1 (p.1.arguments.zip p.2.2.2.1) bs ∧
  ExtrasRelated F p.2.2.1 es p.2.2.2.2

def FamilyRelated (F : Inputs S) (M : Code) : Prop :=
  ∀ p c bs es, OwnerRelated F p bs es →
  StructuralActions.markedAction (domain F) F.data.sourceHeads M p = some c →
  Related F p.2.1 p.2.2.1 c (some (.marked p.1 p.2.1 bs es))

def StagePreservation : Prop := ∀ S (F : Inputs S) M,
  M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads →
  FamilyRelated F M → FamilyRelated F (MarkedConstructorOperator.step S (domain F) F.data.sourceHeads M)

def IterationSound : Prop := ∀ S (F : Inputs S) n,
  FamilyRelated F (MarkedConstructorOperator.iterate S (domain F) F.data.sourceHeads n)

end LogicLineages.PersistentMarking.ProtectedSpineSoundStageTargets
