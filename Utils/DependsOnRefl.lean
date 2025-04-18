import WFC.Ch3_Interpretation


-- The reflexive closure of `DependsOn`.
inductive DefList.DependsOnRefl
  (getDef: GetDef sig)
:
  Nat → Nat → Prop
where
| Refl x: DependsOnRefl getDef x x
| Rec
  (aUsesB: (getDef a).IsFreeVar Set.empty b)
  (bUsesC: DependsOnRefl getDef b c)
  :
    DependsOnRefl getDef a c

def DefList.DependsOn.toDependsOnRefl
  {getDef: GetDef sig}
  (dependsOn: DefList.DependsOn getDef a b)
:
  DependsOnRefl getDef a b
:=
  dependsOn.rec
    (fun isFree => DependsOnRefl.Rec isFree (DependsOnRefl.Refl _))
    (fun isFree _ => DependsOnRefl.Rec isFree)

def DefList.DependsOnRefl.toRflOrDependsOn
  {getDef: GetDef sig}
  (dependsOn: DependsOnRefl getDef a b)
:
  a = b ∨ DependsOn getDef a b
:=
  -- Lean cannot verify termination here :/
  dependsOn.rec
    (fun _ => Or.inl rfl)
    (fun isFree _ => fun
    | Or.inl eq => eq ▸ Or.inr (DependsOn.Base isFree)
    | Or.inr depOn => Or.inr (DependsOn.Rec isFree depOn))

def DefList.DependsOnRefl.push
  {getDef: GetDef sig}
  (dependsOn: DependsOnRefl getDef a b)
  (isFree: (getDef b).IsFreeVar Set.empty c)
:
  DependsOnRefl getDef a c
:=
  match dependsOn.toRflOrDependsOn with
  | Or.inl eq => eq ▸ Rec isFree (Refl _)
  | Or.inr depOn => (depOn.push isFree).toDependsOnRefl


-- A helper version of `IsFinBounded` that includes the definition
-- itself in the upper bound. Useful for consuming the proof.
def DefList.IsFinBoundedRefl (getDef: GetDef sig): Prop :=
  ∀ name,
  ∃ upperBound,
  ∀ {dep}
    (_: DefList.DependsOnRefl getDef name dep)
  ,
    dep < upperBound

def FinBoundedDL.isFinBoundedRefl
  (dl: FinBoundedDL sig)
:
  DefList.IsFinBoundedRefl dl.getDef
:=
  fun x =>
    let ⟨ub, depLeUb⟩ := dl.isFinBounded x
    ⟨
      max ub x.succ,
      fun depOnR =>
        match depOnR.toRflOrDependsOn with
        | Or.inl eq => eq ▸ lt_max_of_lt_right (Nat.lt_succ_self x)
        | Or.inr depOn => lt_max_of_lt_left (depLeUb depOn)
    ⟩
