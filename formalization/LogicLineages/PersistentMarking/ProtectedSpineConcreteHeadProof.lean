import LogicLineages.PersistentMarking.ProtectedSpineFixedHeadProof
import LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof

namespace LogicLineages.PersistentMarking.ProtectedSpineConcreteHeadProof
open Spine DecisionPorts DecisionInventory DecisionSourceUniverse FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter
open ProtectedSpineBoundTargets ProtectedSpineFixedApplicationTargets ProtectedSpineConcreteInputProof
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step)

theorem substitutedCoverage (E : Environment) (H : List Head) (types : List Ty)
    (vs xs : Args) (hv : BoundImages E H vs types)
    (ht : ExtrasTyped (BoundContext.prefix types EmptyContext) xs) (hx : ArgsCovered E H xs) :
    ArgsCovered E H (substituteArgs vs 0 xs) := by
  let V := freeInventoryArgs xs ++ freeInventoryArgs vs
  have hv' : ArgsUniverse E.types V H [] vs :=
    (DecisionSourceBasicProof.argsFacts E.types V H [] vs).mpr
      ⟨hv.2.1,hv.2.2,fun n hn => Or.inl
        (List.mem_append_right _ ((DecisionInventoryProof.freeExactArgs vs n).mpr hn))⟩
  have hx' : ArgsUniverse E.types V H [] xs :=
    (DecisionSourceBasicProof.argsFacts E.types V H [] xs).mpr
      ⟨hx.1,hx.2,fun n hn => Or.inl
        (List.mem_append_left _ ((DecisionInventoryProof.freeExactArgs xs n).mpr hn))⟩
  have h := DecisionSourceSubstitutionProof.extrasPreserves E.types V H []
    (BoundContext.prefix types EmptyContext) EmptyContext vs 0 xs
    (SpineSubstitutionProof.finiteCompatible _ _ _ hv.1) ht hx' hv'
  have he := (DecisionSourceBasicProof.argsFacts E.types V H [] _).mp h
  exact ⟨he.1,he.2.1⟩

theorem substitutedCodes (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ : Context) (types : List Ty) (vs xs : Args)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H)
    (hw : WellFormed E.types E.ports Γ) (hv : BoundImages E H vs types)
    (ht : ExtrasTyped (BoundContext.prefix types EmptyContext) xs) (hx : ArgsCovered E H xs) :
    evaluateArgs S E H M xs Γ [] (closedCodes S E H M Γ vs) =
      closedCodes S E H M Γ (substituteArgs vs 0 xs) :=
  ProtectedSpineBoundSubstitutionProof.arguments S E H M vs types hc hm hv xs [] ht hx
    Γ ⟨[],closedCodes S E H M Γ vs⟩ ⟨[],[]⟩
    (boundValid S E H M Γ vs types hc hm hw hv) (emptyValid E Γ hw) (boundRelation S E H M Γ vs)

theorem headCall (S : Signature) (E : Environment) (H : List Head) (M : Code) (Γ : Context)
    (f : Head) (σ τ : Ty) (bs es : Args) (a : Expr) (args vs : Args) (types : List Ty)
    (hc : PrefixClosed E) (hm : M ∈ MarkedFamilyCoherence.retained E H) (hfix : step S E H M = M)
    (hw : WellFormed E.types E.ports Γ) (hv : BoundImages E H vs types)
    (hf : f ∈ H) (hσ : σ ∈ E.types)
    (ht : BaseTyped (BoundContext.prefix types EmptyContext) bs f.arguments) (hb : ArgsCovered E H bs)
    (he : ExtrasTyped (BoundContext.prefix types EmptyContext) es) (hes : ArgsCovered E H es)
    (ha : CallTyped EmptyContext σ (.cons a args) τ) (has : ArgsCovered E H (.cons a args)) :
    originalHeadCall E H M Γ f σ ((evaluateArgs S E H M bs Γ [] (closedCodes S E H M Γ vs)).map Prod.snd)
      (MarkedExtras.down E Γ (evaluateArgs S E H M es Γ [] (closedCodes S E H M Γ vs)))
      (domainTypes (.cons a args)) ((closedCodes S E H M Γ (.cons a args)).map Prod.snd) τ =
      concreteOutput S E H M Γ τ
        (some (.marked f τ (substituteArgs vs 0 bs) ((substituteArgs vs 0 es).append (.cons a args)))) := by
  have hBase := DecisionOccurrenceProof.baseExtras _ bs f.arguments ht
  rw [substitutedCodes S E H M Γ types vs bs hc hm hw hv hBase hb,
    substitutedCodes S E H M Γ types vs es hc hm hw hv he hes]
  exact ProtectedSpineFixedHeadProof.afterAppend S E H M Γ f σ τ (substituteArgs vs 0 bs)
    (substituteArgs vs 0 es) (.cons a args) hc hm hfix hw hf
    (hc σ hσ _ τ (fullPrefix σ a args τ ha)).1
    (SpineSubstitutionProof.parallelBasePreserves EmptyContext types vs bs f.arguments hv.1 ht)
    (substitutedCoverage E H types vs bs hv hBase hb)
    (SpineSubstitutionProof.parallelExtrasPreserves EmptyContext types vs es hv.1 he)
    (substitutedCoverage E H types vs es hv he hes) ha has

end LogicLineages.PersistentMarking.ProtectedSpineConcreteHeadProof
