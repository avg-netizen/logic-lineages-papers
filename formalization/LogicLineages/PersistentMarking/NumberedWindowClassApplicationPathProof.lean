import LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathTargets
import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassEdge

namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathProof
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowClassApplicationPath NumberedWindowClassApplicationPathTargets
open NumberedWindowClassApplicationHopChecks NumberedWindowClassPathWitnessBits
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticPathCodeChecks
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticScalarTargets NumberedWindowScalarAlgorithm NumberedWindowExternalApplication
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticFieldAlgorithmChecks
open NumberedWindowArithmeticWitnessListCode NumberedWindowArithmeticFieldsProof

private theorem decodeArgument {S : Signature} {K Γ : List Ty} {σ : Ty}
    (hk : DecisionSourceUniverse.Closed K) {a : Nat}
    {u : Class S K (finiteC Γ) σ} (hu : ActualCodeAt S K Γ σ a u) :
    ∃ U, decodeTerm a = some U := by
  have valid := (NumberedWindowArithmeticAllContextAdmittedProof.canonical
    S K ⟨Γ,σ,a⟩ hk).mpr ⟨u,hu⟩
  cases h : decodeTerm a with
  | none => simp [canonicalBit,h] at valid
  | some U => exact ⟨U,rfl⟩

private theorem walkLift {S : Signature} {K Γ : List Ty} {σ τ : Ty}
    (hk : DecisionSourceUniverse.Closed K) (u : Class S K (finiteC Γ) σ)
    {a : Nat} {U : NTerm} (hu : ActualCodeAt S K Γ σ a u) (hU : decodeTerm a = some U)
    (path : List ClassHop) :
    ∀ (i j x : Nat) (q r : Class S K (finiteC Γ) (.arrow σ τ)),
      ActualCodeAt S K Γ (.arrow σ τ) i q →
      ActualCodeAt S K Γ (.arrow σ τ) j r →
      ActualCodeAt S K Γ τ x (appClass hk q u) →
      classWalkBit S K Γ (.arrow σ τ) i path j = true →
        ∃ (y : Nat) (new : List ClassHop),
          (∀ done : List Nat,
            (path.map encodeClassHop).foldl
              (advance (least (fixed S K) (Γ.map encodeTy) (encodeTy τ))
                (encodeTy σ) (encodeTy τ) a) (some (x,done)) =
              some (y,(new.map encodeClassHop).reverse ++ done)) ∧
          AlignedHops σ τ U path new ∧
          classWalkBit S K Γ τ x new y = true ∧
          ActualCodeAt S K Γ τ y (appClass hk r u) := by
  induction path with
  | nil =>
    intro i j x q r hq hr hx hwalk
    simp only [classWalkBit,decide_eq_true_eq] at hwalk
    subst j
    have eq := sameClass hk hq hr
    subst r
    exact ⟨x,[],fun _ => rfl,.nil,by simp [classWalkBit],hx⟩
  | cons first tail ih =>
    intro i j x q r hq hr hx hwalk
    simp only [classWalkBit,Bool.and_eq_true] at hwalk
    obtain ⟨_,middle,_,hm,_⟩ := NumberedWindowPathWitnessClassEdge.sound hwalk.1
    obtain ⟨U',x',m',hU',packed,valid,hx',hm'⟩ :=
      exact_ClassHopLift S K Γ σ τ hk q middle u i first.targetCode a first.edge
        hq hm hu hwalk.1
    have sameArgument : U' = U := Option.some.inj (hU'.symm.trans hU)
    subst U'
    have sameImage : x' = x := sameCode hk hx' hx
    subst x'
    obtain ⟨y,news,folded,related,validTail,hy⟩ := ih first.targetCode j m'
      middle r hm hr hm' hwalk.2
    let lifted : ClassHop := ⟨m',
      ⟨.auxApp σ τ first.edge.source U,.auxApp σ τ first.edge.target U,
        .auxFunction first.edge.witness⟩⟩
    refine ⟨y,lifted :: news,?_,.cons rfl related,?_,hy⟩
    · intro done
      simp only [List.map_cons,List.foldl_cons,advance,Option.bind_eq_bind,
        Option.bind_some,packed,beq_self_eq_true,if_true]
      rw [folded (encodeClassHop lifted :: done)]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    · simp only [classWalkBit,Bool.and_eq_true]
      exact ⟨valid,validTail⟩

private theorem nonempty {σ τ : Ty} {U : NTerm} {old new : List ClassHop}
    (h : AlignedHops σ τ U old new) :
    (!old.isEmpty) = true → (!new.isEmpty) = true := by
  cases h <;> simp

theorem exactPath : ExactPositiveClassPathLift := by
  intro S K Γ σ τ hk q r u i j a imageSource certificate hq hr hu hx valid
  obtain ⟨U,hU⟩ := decodeArgument hk hu
  cases read : decodeClassPath certificate with
  | none => simp [positiveClassPathCodeBit,read] at valid
  | some old =>
    simp only [positiveClassPathCodeBit,read,positiveClassPathBit,Bool.and_eq_true] at valid
    have codeOld := (exact_ClassPathListCodec.1 certificate old).mp read
    have unpackOld : NumberedWindowFieldAlgorithm.unpack certificate =
        some (old.map encodeClassHop) := by
      rw [← codeOld,encodeClassPath,encodeListOf,← exact_ExactOrderedFieldCodec.2]
      exact fieldsRound _
    have guard : (old.map encodeClassHop).isEmpty = false := by
      cases old with
      | nil => simp at valid
      | cons _ _ => rfl
    obtain ⟨y,newPath,folded,related,validNew,hy⟩ :=
      walkLift hk u hu hU old i j imageSource q r hq hr hx valid.2
    have readNew := exact_ClassPathListCodec.2.1 newPath
    refine ⟨y,encodeClassPath newPath,U,old,newPath,hU,?_,readNew,related,?_,?_,hy⟩
    · first | exact read | rfl
    · have done := folded []
      simp only [List.append_nil] at done
      simp only [liftPath,unpackOld,Option.bind_eq_bind,Option.bind_some,guard,Bool.false_eq_true,if_false,
        done,List.reverse_reverse,Option.pure_def,encodeClassPath,encodeListOf,exact_ExactOrderedFieldCodec.1]
    · simp only [positiveClassPathCodeBit,readNew,positiveClassPathBit,Bool.and_eq_true]
      exact ⟨nonempty related valid.1,validNew⟩

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathProof
