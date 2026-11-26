module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalSubstitutionTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationPrimaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionPrimaryProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowExternalSubstitutionTargets NumberedWindowPreservationGuardProof
open NumberedWindowPreservationBoundProof (Compatible push one)
open NumberedWindowPreservationSubstitutionProof (term base extras)
open NumberedWindowNumberedDomainProof (ArgsGuard parts)
open NumberedWindowPreservationReplacementProof (permGuard)

private theorem toListSubstitute (values : NArgs) (d : Nat) (xs : NArgs) :
    (substituteArgs values d xs).toList = xs.toList.map (substitute values d) := by
  cases xs with
  | nil => rfl
  | cons a rest => simp only [substituteArgs, NArgs.toList, List.map_cons, toListSubstitute values d rest]
termination_by sizeOf xs

private theorem substPerm (values : NArgs) (d : Nat) {xs ys : NArgs}
    (h : xs.toList.Perm ys.toList) :
    (substituteArgs values d xs).toList.Perm (substituteArgs values d ys).toList := by
  simpa only [toListSubstitute] using h.map (substitute values d)

private def TermClaim (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty)
    (q r : NTerm) : Prop :=
  (Typed C q τ ∧ Typed C r τ) ∧ ∀ values d D, Compatible S K values d C D →
    TermGuard S K q → Primary S K D τ (substitute values d q) (substitute values d r)

private def ArgsClaim (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (types : List Ty) (xs ys : NArgs) : Prop :=
  (BaseTyped C xs types ∧ BaseTyped C ys types) ∧ ∀ values d D, Compatible S K values d C D →
    ArgsGuard S K xs → OrderedPrimary S K D types (substituteArgs values d xs) (substituteArgs values d ys)

private theorem both {S K C τ q r} (hk : DecisionSourceUniverse.Closed K)
    (h : Primary S K C τ q r) : TermClaim S K C τ q r := by
  induction h using Primary.rec (motive_2 := fun C types xs ys _ => ArgsClaim S K C types xs ys) with
  | refl ht =>
    refine ⟨⟨ht, ht⟩, ?_⟩
    intro values d D hc hg
    exact .refl (term S K hk values d _ D _ _ ⟨ht, hg⟩ hc).1
  | symm hp ih =>
    refine ⟨⟨ih.1.2, ih.1.1⟩, ?_⟩
    intro values d D hc hg
    have hBefore := (NumberedWindowPreservationPrimaryProof.primary hk hp).mpr ⟨ih.1.2, hg⟩
    exact .symm (ih.2 values d D hc hBefore.2)
  | trans hp _ hq hr =>
    refine ⟨⟨hq.1.1, hr.1.2⟩, ?_⟩
    intro values d D hc hg
    have hMiddle := (NumberedWindowPreservationPrimaryProof.primary hk hp).mp ⟨hq.1.1, hg⟩
    exact .trans (hq.2 values d D hc hg) (hr.2 values d D hc hMiddle.2)
  | ordinary hf hg he hType hbs hcs hp =>
    refine ⟨⟨.ordinary hbs, hType.symm ▸ Typed.ordinary hcs⟩, ?_⟩
    intro values d D hc hGuard
    have hSource := (ordinaryParts ⟨Typed.ordinary hbs, hGuard⟩).2.2
    exact .ordinary hf hg he hType
      (base S K hk values d _ D _ _ hbs hSource hc).1
      (base S K hk values d _ D _ _ hcs (permGuard hp hSource) hc).1 (substPerm values d hp)
  | numbered hf hg he hbs hcs hes hp =>
    refine ⟨⟨.numbered hbs hes, .numbered hcs hes⟩, ?_⟩
    intro values d D hc hGuard
    have hSource := parts ⟨Typed.numbered hbs hes, hGuard⟩
    exact .numbered hf hg he
      (base S K hk values d _ D _ _ hbs hSource.2.2.2.1 hc).1
      (base S K hk values d _ D _ _ hcs (permGuard hp hSource.2.2.2.1) hc).1
      (extras S K hk values d _ D _ hes hSource.2.2.2.2 hc).1 (substPerm values d hp)
  | lam _ ih =>
    refine ⟨⟨.lam ih.1.1, .lam ih.1.2⟩, ?_⟩
    intro values d D hc hg
    exact .lam (ih.2 values (d + 1) _ (push hk hc) (lamBody ⟨.lam ih.1.1, hg⟩).2)
  | appFunction _ ha ih =>
    refine ⟨⟨.auxApp ih.1.1 ha, .auxApp ih.1.2 ha⟩, ?_⟩
    intro values d D hc hg
    obtain ⟨hq, hu⟩ := appParts ⟨.auxApp ih.1.1 ha, hg⟩
    exact .appFunction (ih.2 values d D hc hq.2) (term S K hk values d _ D _ _ hu hc).1
  | appArgument hf _ ih =>
    refine ⟨⟨.auxApp hf ih.1.1, .auxApp hf ih.1.2⟩, ?_⟩
    intro values d D hc hg
    obtain ⟨hq, hu⟩ := appParts ⟨.auxApp hf ih.1.1, hg⟩
    exact .appArgument (term S K hk values d _ D _ _ hq hc).1 (ih.2 values d D hc hu.2)
  | ordinaryArguments _ ih =>
    refine ⟨⟨.ordinary ih.1.1, .ordinary ih.1.2⟩, ?_⟩
    intro values d D hc hg
    exact .ordinaryArguments (ih.2 values d D hc (ordinaryParts ⟨.ordinary ih.1.1, hg⟩).2.2)
  | numberedBase _ he ih =>
    refine ⟨⟨.numbered ih.1.1 he, .numbered ih.1.2 he⟩, ?_⟩
    intro values d D hc hg
    have hParts := parts ⟨Typed.numbered ih.1.1 he, hg⟩
    exact .numberedBase (ih.2 values d D hc hParts.2.2.2.1)
      (extras S K hk values d _ D _ he hParts.2.2.2.2 hc).1
  | numberedExtras hb _ ih =>
    refine ⟨⟨.numbered hb (toExtras ih.1.1), .numbered hb (toExtras ih.1.2)⟩, ?_⟩
    intro values d D hc hg
    have hParts := parts ⟨Typed.numbered hb (toExtras ih.1.1), hg⟩
    exact .numberedExtras (base S K hk values d _ D _ _ hb hParts.2.2.2.1 hc).1
      (ih.2 values d D hc hParts.2.2.2.2)
  | nil => exact ⟨⟨.nil, .nil⟩, fun _ _ _ _ _ => .nil⟩
  | cons _ _ ha hs =>
    refine ⟨⟨.cons ha.1.1 hs.1.1, .cons ha.1.2 hs.1.2⟩, ?_⟩
    intro values d D hc hg
    obtain ⟨hHead, hTail⟩ := consParts hg
    exact .cons (ha.2 values d D hc hHead) (hs.2 values d D hc hTail)

theorem compatible : CompatibleBodySubstitutionPrimary := by
  intro S K values d C D τ q r hk hc hq hp
  exact (both hk hp).2 values d D hc hq.2

theorem literalBody : LiteralBodyClassSubstitution := by
  intro S K C σ τ hk q r u
  refine ⟨rfl, ?_⟩
  intro h
  have hPrimary := NumberedWindowExternalNeutralPrimaryProof.primaryOfClassEquality q r h
  exact Quot.sound (compatible S K _ 0 _ C τ q.val r.val hk (one hk u.property) q.property hPrimary)

end LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionPrimaryProof
