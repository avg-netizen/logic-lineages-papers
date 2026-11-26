module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepAssembleProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalAccessibilityRules (certificate edge carrier)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists edgeSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename packedBodyRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules exact_DomainRules)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)
open NumberedWindowInternalLiteralSingletonStepAssembleProof
  (singletonRow singletonWitness exact_OriginalSingletonOddFromReports)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
abbrev D (p : Formula α) := Nonempty (Derivation B Γ p)

theorem singletonCodeRename {α β : Type} (x : OTerm α) (j : α → β) :
    (singletonCode x).relabel j = singletonCode (x.relabel j) := by
  simp only [singletonCode,rawConsRename,zRelabel]

private theorem tagTripleRename {α β : Type} (tag : Nat) (a b c : OTerm α) (j : α → β) :
    (tripleTerm tag a b c).relabel j = tripleTerm tag (a.relabel j) (b.relabel j) (c.relabel j) := by
  simp only [tripleTerm,rawConsRename,numeralRename,packedBodyRename,List.map_cons,List.map_nil]

private theorem rowRename {α β : Type} (x w y : OTerm α) (j : α → β) :
    (singletonRow x w y).relabel j = singletonRow (x.relabel j) (w.relabel j) (y.relabel j) := by
  unfold singletonRow
  rw [tagTripleRename]

private theorem witnessRename {α β : Type} (x w y : OTerm α) (j : α → β) :
    (singletonWitness x w y).relabel j = singletonWitness (x.relabel j) (w.relabel j) (y.relabel j) := by
  simp only [singletonWitness,tagTripleRename,rawConsRename,rowRename,singletonCodeRename,zRelabel]

private theorem certRename {α β : Type} (S : Data) (odd : Bool) (c : Nat) (x y w : OTerm α) (j : α → β) :
    (certificate S odd c x y w).relabel j =
      certificate S odd c (x.relabel j) (y.relabel j) (w.relabel j) := by
  unfold certificate
  rw [programRename,sucRelabel,zRelabel]
  congr 1
  funext k
  exact Fin.cases (numeralRename _ j)
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) k

private theorem consCases (h t : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (s : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D (B := B) (Γ := Δ) (consGraph s (h.relabel j) (t.relabel j)) →
      D (B := B) (Γ := Δ) (goal.relabel j)) :
    D (B := B) (Γ := Γ) goal := by
  apply programCases consCode ![h,t] goal
  intro β j Δ s keep result
  rw [binaryInputsRename] at result
  exact next β j Δ s keep result

private theorem moveCons {α β : Type} {B : Positive (Fin 1)} {Γ : List (Formula α)} {Δ : List (Formula β)}
    (s h : OTerm α) (held : D (B := B) (Γ := Γ) (consGraph s h z))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    D (B := B) (Γ := Δ) (consGraph (s.relabel j) (h.relabel j) z) := by
  simpa only [consGraphRename,zRelabel] using renameInto held j Δ keep

/-- Specialize the literal direct checker at the real scalar certificate.
The scratch lists used in reconstruction are generated by its actual
codec, not hypothesized by the user of the theorem. -/
theorem exact_OriginalSingletonCertificateLift (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x y w : OTerm α)
    (hx : D (B := sourceBody (literalData i r) c) (Γ := Γ) (carrier (literalData i r) false c x))
    (hy : D (B := sourceBody (literalData i r) c) (Γ := Γ) (carrier (literalData i r) false c y))
    (he : D (B := sourceBody (literalData i r) c) (Γ := Γ) (certificate (literalData i r) false c x y w)) :
    D (B := sourceBody (literalData i r) c) (Γ := Γ)
      (certificate (literalData i r) true c (singletonCode x) (singletonCode y) (singletonWitness x w y)) := by
  let S := literalData i r
  let B := sourceBody S c
  let goal := certificate S true c (singletonCode x) (singletonCode y) (singletonWitness x w y)
  let jRaw := jRaw i
  let d := dCore i r permutation
  have rawX : D (B := B) (Γ := Γ) (unary i (suc z) x) := (exact_DomainRules i jRaw r d false c B α Γ x).1 hx
  have rawY : D (B := B) (Γ := Γ) (unary i (suc z) y) := (exact_DomainRules i jRaw r d false c B α Γ y).1 hy
  have rawEdge : D (B := B) (Γ := Γ) (programGraph r (suc z) ![x,w,y]) :=
    (exact_CertificateRules i jRaw r d false c B α Γ x y w).1 he
  apply consCases x z goal
  intro β j Δ xs keep hs
  rw [zRelabel] at hs
  rw [certRename,singletonCodeRename,singletonCodeRename,witnessRename]
  let x₁ := x.relabel j
  let y₁ := y.relabel j
  let w₁ := w.relabel j
  let next := certificate S true c (singletonCode x₁) (singletonCode y₁) (singletonWitness x₁ w₁ y₁)
  apply consCases y₁ z next
  intro γ k Ξ ys keeps ht
  rw [zRelabel] at ht
  rw [certRename,singletonCodeRename,singletonCodeRename,witnessRename]
  let x₂ := x₁.relabel k
  let y₂ := y₁.relabel k
  let w₂ := w₁.relabel k
  let last := certificate S true c (singletonCode x₂) (singletonCode y₂) (singletonWitness x₂ w₂ y₂)
  apply consCases (singletonRow x₂ w₂ y₂) z last
  intro δ l Ω rows preserve hr
  rw [rowRename,zRelabel] at hr
  rw [certRename,singletonCodeRename,singletonCodeRename,witnessRename]
  let lift : α → δ := l ∘ k ∘ j
  have liftKeep (p : Formula α) (m : p ∈ Γ) : p.relabel lift ∈ Ω := by
    simpa only [formulaRelabelComposition,lift,Function.comp_assoc] using
      preserve _ (keeps _ (keep p m))
  have newX : D (B := B) (Γ := Ω) (unary i (suc z) (x₂.relabel l)) := by
    simpa only [unaryRename,sucRelabel,zRelabel,Term.relabel_relabel,x₂,x₁,lift,Function.comp_assoc]
      using renameInto rawX lift Ω liftKeep
  have newY : D (B := B) (Γ := Ω) (unary i (suc z) (y₂.relabel l)) := by
    simpa only [unaryRename,sucRelabel,zRelabel,Term.relabel_relabel,y₂,y₁,lift,Function.comp_assoc]
      using renameInto rawY lift Ω liftKeep
  have actual := renameInto rawEdge lift Ω liftKeep
  rw [programRename,sucRelabel,zRelabel] at actual
  have tape : (fun t : Fin 3 => (![x,w,y] t).relabel lift) =
      ![x₂.relabel l,w₂.relabel l,y₂.relabel l] := by
    funext t
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun p => Fin.elim0 p))) t <;>
      simp only [Term.relabel_relabel,x₂,x₁,y₂,y₁,w₂,w₁,lift] <;> rfl
  rw [tape] at actual
  exact exact_OriginalSingletonOddFromReports i r c δ Ω (x₂.relabel l) (w₂.relabel l) (y₂.relabel l)
    ((xs.relabel k).relabel l) (ys.relabel l) rows
    (moveCons _ _ (moveCons _ _ hs k keeps) l preserve) (moveCons _ _ ht l preserve)
    hr newX newY actual

private theorem oddRename {α β : Type} (S : Data) (c : Nat) (x y : OTerm α)
    (j : α → β) : (edge S true c x y).relabel j =
      edge S true c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge S true c x y).subst (fun n => emb (.var (j n))) = _
  rw [edgeSubst,← termRelabelAsSubst,← termRelabelAsSubst]

/-- Any actual scalar step between held carriers lifts to an odd step on
their exact raw singletons. No scratch or certificate term has to be
exhibited by the consumer. -/
theorem exact_OriginalSingletonEdgeLift (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (x y : OTerm α)
    (hx : D (B := sourceBody (literalData i r) c) (Γ := Γ) (carrier (literalData i r) false c x))
    (hy : D (B := sourceBody (literalData i r) c) (Γ := Γ) (carrier (literalData i r) false c y))
    (he : D (B := sourceBody (literalData i r) c) (Γ := Γ) (edge (literalData i r) false c x y)) :
    D (B := sourceBody (literalData i r) c) (Γ := Γ)
      (edge (literalData i r) true c (singletonCode x) (singletonCode y)) := by
  let S := literalData i r
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := certificate S false c (x.relabel j) (y.relabel j) w
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have left := renameInto hx j Δ keep
  have right := renameInto hy j Δ keep
  rw [carrierRename] at left right
  have oddCert := exact_OriginalSingletonCertificateLift i r c _ Δ (x.relabel j) (y.relabel j) w
    left right (⟨Derivation.hypothesis List.mem_cons_self⟩ : D (B := B) (Γ := Δ) A)
  obtain ⟨lifted⟩ := edgeIntroduction oddCert
  have out : Derivation B Δ (weaken (edge S true c (singletonCode x) (singletonCode y))) := by
    rw [weaken,oddRename,singletonCodeRename,singletonCodeRename]
    exact lifted
  obtain ⟨edge⟩ := he
  rw [edgeExists] at edge
  exact ⟨Derivation.existentialElimination edge out⟩

#print axioms exact_OriginalSingletonCertificateLift
#print axioms exact_OriginalSingletonEdgeLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonStepProof
