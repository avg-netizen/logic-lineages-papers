import LogicLineages.PersistentMarking.ProtectedSpineInterpreterCore

namespace LogicLineages.PersistentMarking.ProtectedSpineInterpreter
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineInterpreterCore

mutual
def evaluate (S : Signature) (E : Environment) (heads : List Head) (M : Code) (q : Expr) : Evaluation :=
  match q with
  | .free σ x =>
    { value := fun Γ free _ => decode E σ Γ (freeCode E Γ free σ x)
      nonempty := fun Γ free _ _ d x₀ ds xs τ =>
        variableCall E σ Γ (freeCode E Γ free σ x) (d::ds) (x₀::xs) τ }
  | .bound σ i =>
    { value := fun Γ _ bound => decode E σ Γ (boundCode E Γ bound σ i)
      nonempty := fun Γ _ bound consumed d x ds xs τ =>
        if protectedLookup consumed i then StructuralActions.bottom E τ Γ
        else variableCall E σ Γ (boundCode E Γ bound σ i) (d::ds) (x::xs) τ }
  | .head f bs =>
    let base := evaluateArgs S E heads M bs
    { value := fun Γ free bound =>
        ordinaryHead S E heads M (parameter E f f.result Γ (base Γ free bound) [])
      nonempty := fun Γ free bound _ d x ds xs τ =>
        originalHeadCall E heads M Γ f f.result ((base Γ free bound).map Prod.snd)
          (MarkedExtras.down E Γ []) (d::ds) (x::xs) τ }
  | .marked f σ bs es =>
    let base := evaluateArgs S E heads M bs
    let extras := evaluateArgs S E heads M es
    { value := fun Γ free bound =>
        MarkedConstructorValue.build S E heads M (parameter E f σ Γ (base Γ free bound) (extras Γ free bound))
      nonempty := fun Γ free bound _ d x ds xs τ =>
        originalHeadCall E heads M Γ f σ ((base Γ free bound).map Prod.snd)
          (MarkedExtras.down E Γ (extras Γ free bound)) (d::ds) (x::xs) τ }
  | .lam σ body =>
    let child := evaluate S E heads M body
    { value := lambdaValue E σ body.type child
      nonempty := lambdaCall E σ body.type child }
termination_by structural q

def evaluateArgs (S : Signature) (E : Environment) (heads : List Head) (M : Code) (qs : Args) :
    Context → FreeValues → BoundValues → BoundValues :=
  match qs with
  | .nil => fun _ _ _ => []
  | .cons q rest =>
    let x := evaluate S E heads M q
    let xs := evaluateArgs S E heads M rest
    fun Γ free bound => (q.type,code E q.type Γ (x.value Γ free bound))::xs Γ free bound
termination_by structural qs
end

def interpret (S : Signature) (E : Environment) (heads : List Head) (M : Code) (q : Expr)
    (Γ : Context) (free : FreeValues) (bound : BoundValues) : Value :=
  (evaluate S E heads M q).value Γ free bound

def call (S : Signature) (E : Environment) (heads : List Head) (M : Code) (q : Expr)
    (Γ : Context) (free : FreeValues) (bound : BoundValues)
    (domains : List Ty) (values : List Code) (τ : Ty) : Code :=
  match domains,values with
  | [],[] =>
    if q.type=τ then code E τ Γ (interpret S E heads M q Γ free bound) else StructuralActions.bottom E τ Γ
  | d::ds,x::xs => (evaluate S E heads M q).nonempty Γ free bound 0 d x ds xs τ
  | _,_ => StructuralActions.bottom E τ Γ

end LogicLineages.PersistentMarking.ProtectedSpineInterpreter
