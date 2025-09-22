```lean -show
section
open Lean (TSyntax Name)
variable {c1 c2 : Name} {α : Type u}
```
```lean -show
end
```
```lean
example (n : Nat) : Int := n
example (n : Fin k) : Nat := n
example (x : α) : Option α := x

def th (f : Int → String) (x : Nat) : Thunk String := f x

open Lean in
example (n : Ident) : Term := n
```
```lean (name := thunkEval)
#print th
```
```leanOutput thunkEval
def th : (Int → String) → Nat → Thunk String :=
fun f x => { fn := fun x_1 => f ↑x }
```
```leanOutput thunkEval
def th : (Int → String) → Nat → Thunk String :=
fun f x => { fn := fun x_1 => f ↑x }
```
```lean -show
section
variable {α : Type u}
```
```lean -show
end
```
```lean -show
-- Test comment about field notation
/-- error: Unknown constant `Nat.bdiv` -/
#check_msgs in
#check Nat.bdiv

/-- info: Int.bdiv (x : Int) (m : Nat) : Int -/
#check_msgs in
#check Int.bdiv

/--
error: Invalid field `bdiv`: The environment does not contain `Nat.bdiv`
  n
has type
  Nat
-/
#check_msgs in
example (n : Nat) := n.bdiv 2

#check_msgs in
example (n : Nat) := (n : Int).bdiv 2
```
```lean +error (name := natBdiv)
example (n : Nat) := n.bdiv 2
```
```leanOutput natBdiv
Invalid field `bdiv`: The environment does not contain `Nat.bdiv`
  n
has type
  Nat
```
```leanOutput natBdiv
Invalid field `bdiv`: The environment does not contain `Nat.bdiv`
  n
has type
  Nat
```
```lean
example (n : Nat) := (n : Int).bdiv 2
```
```lean
inductive Bin where
  | done
  | zero : Bin → Bin
  | one : Bin → Bin

def Bin.toString : Bin → String
  | .done => ""
  | .one b => b.toString ++ "1"
  | .zero b => b.toString ++ "0"

instance : ToString Bin where
  toString
    | .done => "0"
    | b => Bin.toString b
```
```lean
def Bin.succ (b : Bin) : Bin :=
  match b with
  | .done => Bin.done.one
  | .zero b => .one b
  | .one b => .zero b.succ

def Bin.ofNat (n : Nat) : Bin :=
  match n with
  | 0 => .done
  | n + 1 => (Bin.ofNat n).succ
```
```lean -show
--- Internal tests
/-- info: [0, 1, 10, 11, 100, 101, 110, 111, 1000] -/
#check_msgs in
#eval [
  Bin.done,
  Bin.done.succ,
  Bin.done.succ.succ,
  Bin.done.succ.succ.succ,
  Bin.done.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ.succ]

def Bin.toNat : Bin → Nat
  | .done => 0
  | .zero b => 2 * b.toNat
  | .one b => 2 * b.toNat + 1

def Bin.double : Bin → Bin
  | .done => .done
  | other => .zero other

theorem Bin.toNat_succ_eq_succ {b : Bin} : b.toNat = n → b.succ.toNat = n + 1 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.succ]

theorem Bin.toNat_double_eq_double {b : Bin} : b.toNat = n → b.double.toNat = n * 2 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.double]

theorem Bin.ofNat_toNat_eq {n : Nat} : (Bin.ofNat n).toNat = n := by
  induction n <;> simp_all [Bin.ofNat, Bin.toNat, Bin.toNat_succ_eq_succ]
```
```lean (name := nineFail) +error
attribute [coe] Bin.ofNat

instance : Coe Nat Bin where
  coe := Bin.ofNat

#eval (9 : Bin)
```
```leanOutput nineFail
failed to synthesize
  OfNat Bin 9
numerals are polymorphic in Lean, but the numeral `9` cannot be used in a context where the expected type is
  Bin
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput nineFail
failed to synthesize
  OfNat Bin 9
numerals are polymorphic in Lean, but the numeral `9` cannot be used in a context where the expected type is
  Bin
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean (name := ten)
instance : OfNat Bin n where
  ofNat := n

#eval (10 : Bin)
```
```leanOutput ten
1010
```
```leanOutput ten
1010
```
```lean
structure Decimal where
  digits : Array (Fin 10)
```
```lean
@[coe]
def Decimal.toNat (d : Decimal) : Nat :=
  d.digits.foldl (init := 0) fun n d => n * 10 + d.val

instance : Coe Decimal Nat where
  coe := Decimal.toNat
```
```lean (name := digival)
def twoHundredThirteen : Decimal where
  digits := #[2, 1, 3]

def one : Decimal where
  digits := #[1]

#eval (one : Int) - (twoHundredThirteen : Nat)
```
```leanOutput digival
-212
```
```leanOutput digival
-212
```
```lean -show
section
variable {α : Type u} {α' : Type u'} {β : Type u} [Coe α α'] [Coe α' β] (e : α)
```
```lean -show
end
```
```lean
structure Later (α : Type u) where
  get : Unit → α
```
```lean
instance : CoeTail α (Later α) where
  coe x := { get := fun () => x }
```
```lean
def tomorrow : Later String :=
  (Nat.fold 10000
    (init := "")
    (fun _ _ s => s ++ "tomorrow") : String)
```
```lean (name := tomorrow)
#print tomorrow
```
```leanOutput tomorrow
def tomorrow : Later String :=
{ get := fun x => Nat.fold 10000 (fun x x s => s ++ "tomorrow") "" }
```
```leanOutput tomorrow
def tomorrow : Later String :=
{ get := fun x => Nat.fold 10000 (fun x x s => s ++ "tomorrow") "" }
```
```lean -show
section
variable {α : Type u}
```
```lean
structure Twice (α : Type u) where
  first : α
  second : α
  first_eq_second : first = second
```
```lean
@[coe]
def twice (x : α) : Twice α where
  first := x
  second := x
  first_eq_second := rfl

instance : Coe α (Twice α) := ⟨twice⟩
```
```lean (name := eval1)
#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval1
hello
```
```leanOutput eval1
hello
```
```lean (name := eval2)
instance : Coe α (Twice α) where
  coe x := ⟨x, x, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval2
hello
hello
```
```leanOutput eval2
hello
hello
```
```lean (name := eval3)
instance : Coe α (Twice α) where
  coe x := let y := x; ⟨y, y, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval3
hello
```
```leanOutput eval3
hello
```
```lean -show
end
```
```lean
structure Even where
  number : Nat
  isEven : number % 2 = 0
```
```lean
attribute [coe] Even.number

instance : Coe Even Nat where
  coe := Even.number
```
```lean (name := four)
def four : Even := ⟨4, by omega⟩

#eval (four : Nat) + 1
```
```leanOutput four
5
```
```leanOutput four
5
```
```lean (name := four')
#eval (four : Int) - 5
```
```leanOutput four'
-1
```
```leanOutput four'
-1
```
```lean (name := fourCoe)
instance : CoeDep String "four" Nat where
  coe := 4

#eval ("four" : Nat)
```
```leanOutput fourCoe
4
```
```leanOutput fourCoe
4
```
```lean +error (name := threeCoe)
#eval ("three" : Nat)
```
```leanOutput threeCoe
Type mismatch
  "three"
has type
  String
but is expected to have type
  Nat
```
```leanOutput threeCoe
Type mismatch
  "three"
has type
  String
but is expected to have type
  Nat
```
```lean -show
section
variable {α α' α'' β β' «…» γ: Sort _}

macro "…":term => Lean.mkIdentFromRef `«…»

variable [CoeHead α α'] [CoeOut α' …] [CoeOut … α''] [Coe α'' …] [Coe … β'] [CoeTail β' γ]


```
```lean
structure Truthy (α : Type) where
  val : α
  isTrue : Bool

inductive Decision (α : Type) where
  | yes
  | maybe (val : α)
  | no
```
```lean
@[coe]
def Truthy.toBool : Truthy α → Bool :=
  Truthy.isTrue

@[coe]
def Decision.ofBool : Bool → Decision α
  | true => .yes
  | false => .no
```
```lean
instance : CoeOut (Truthy α) Bool := ⟨Truthy.isTrue⟩

instance : Coe Bool (Decision α) := ⟨Decision.ofBool⟩
```
```lean (name := chainTruthiness)
#eval ({ val := 1, isTrue := true : Truthy Nat } : Decision String)
```
```leanOutput chainTruthiness
Decision.yes
```
```leanOutput chainTruthiness
Decision.yes
```
```lean (name := coeOutErr) +error
instance : Coe (Truthy α) Bool := ⟨Truthy.isTrue⟩
```
```leanOutput coeOutErr
instance does not provide concrete values for (semi-)out-params
  Coe (Truthy ?α) Bool
```
```leanOutput coeOutErr
instance does not provide concrete values for (semi-)out-params
  Coe (Truthy ?α) Bool
```
```lean -show
end
```
```lean -show
section
variable {α β : Sort _} {e : α} [CoeDep α e β]
```
```lean -show
end
```
```lean -show
universe u
```
```lean
structure NonEmptyList (α : Type u) : Type u where
  contents : List α
  non_empty : contents ≠ []

instance : Coe (NonEmptyList α) (List α) where
  coe xs := xs.contents
```
```lean
def oneTwoThree : NonEmptyList Nat := ⟨[1, 2, 3], by simp⟩

#eval (oneTwoThree : List Nat) ++ [4]
```
```lean +error (name := coeFail) -keep
instance : Coe (List α) (NonEmptyList α) where
  coe xs := ⟨xs, _⟩
```
```leanOutput coeFail
don't know how to synthesize placeholder for argument `non_empty`
context:
α : Type u_1
xs : List α
⊢ xs ≠ []
```
```leanOutput coeFail
don't know how to synthesize placeholder for argument `non_empty`
context:
α : Type u_1
xs : List α
⊢ xs ≠ []
```
```lean (name := coeOk)
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨x :: xs, by simp⟩

#eval ([1, 2, 3] : NonEmptyList Nat)
```
```leanOutput coeOk
{ contents := [1, 2, 3], non_empty := _ }
```
```leanOutput coeOk
{ contents := [1, 2, 3], non_empty := _ }
```
```lean +error (name := coeFailDep)
#check
  fun (xs : List Nat) =>
    let ys : List Nat := xs ++ [4]
    (ys : NonEmptyList Nat)
```
```leanOutput coeFailDep
Type mismatch
  ys
has type
  List Nat
but is expected to have type
  NonEmptyList Nat
```
```leanOutput coeFailDep
Type mismatch
  ys
has type
  List Nat
but is expected to have type
  NonEmptyList Nat
```
```lean (name := subThenCoe)
def sub (n k : Nat) : Int := n - k

#print sub
```
```leanOutput subThenCoe
def sub : Nat → Nat → Int :=
fun n k => ↑n - ↑k
```
```leanOutput subThenCoe
def sub : Nat → Nat → Int :=
fun n k => ↑n - ↑k
```
```lean (name:=coeThenSub)
def sub' (n k : Nat) : Int := ↑ (n - k)

#print sub'
```
```lean (name := subRes)
#eval sub 4 8
```
```leanOutput subRes
-4
```
```leanOutput subRes
-4
```
```lean (name := subMark)
#eval sub' 4 8
```
```leanOutput subMark
0
```
```leanOutput subMark
0
```
```lean
inductive Weekday where
  | mo | tu | we | th | fr | sa | su
```
```lean
def Weekday.toFin : Weekday → Fin 7
  | mo => 0
  | tu => 1
  | we => 2
  | th => 3
  | fr => 4
  | sa => 5
  | su => 6

def Weekday.fromFin : Fin 7 → Weekday
  | 0 => mo
  | 1 => tu
  | 2 => we
  | 3 => th
  | 4 => fr
  | 5 => sa
  | 6 => su
```
```lean -show
theorem Weekday.toFin_fromFin_id : Weekday.toFin (Weekday.fromFin n) = n := by
  repeat (cases ‹Fin (_ + 1)› using Fin.cases; case zero => rfl)
  apply Fin.elim0; assumption

theorem Weekday.fromFin_toFin_id : Weekday.fromFin (Weekday.toFin w) = w := by
  cases w <;> rfl
```
```lean
instance : Coe Weekday (Fin 7) where
  coe := Weekday.toFin

instance : Coe (Fin 7) Weekday where
  coe := Weekday.fromFin
```
```lean (name := wednesday)
def wednesday : Weekday := (2 : Fin 7)

#print wednesday
```
```leanOutput wednesday
def wednesday : Weekday :=
Weekday.fromFin 2
```
```leanOutput wednesday
def wednesday : Weekday :=
Weekday.fromFin 2
```
```lean (name := friday)
attribute [coe] Weekday.fromFin
attribute [coe] Weekday.toFin

def friday : Weekday := (5 : Fin 7)

#print friday
```
```leanOutput friday
def friday : Weekday :=
↑5
```
```leanOutput friday
def friday : Weekday :=
↑5
```
```lean
structure Monoid where
  Carrier : Type u
  op : Carrier → Carrier → Carrier
  id : Carrier
  op_assoc :
    ∀ (x y z : Carrier), op x (op y z) = op (op x y) z
  id_op_identity : ∀ (x : Carrier), op id x = x
  op_id_identity : ∀ (x : Carrier), op x id = x
```
```lean
def StringMonoid : Monoid where
  Carrier := String
  op := (· ++ ·)
  id := ""
  op_assoc := by intros; simp [String.append_assoc]
  id_op_identity := by intros; simp
  op_id_identity := by intros; simp
```
```lean
instance : CoeSort Monoid (Type u) where
  coe m := m.Carrier

example : StringMonoid := "hello"
```
```lean
inductive NatOrBool where
  | nat | bool

@[coe]
abbrev NatOrBool.asType : NatOrBool → Type
  | .nat => Nat
  | .bool => Bool

instance : CoeSort NatOrBool Type where
  coe := NatOrBool.asType

open NatOrBool
```
```lean
def x : nat := 5
```
```lean
def y : Option Type := bool
```
```lean -show
section
variable {α : Type u} {β : Type v}
```
```lean
structure NamedFun (α : Type u) (β : Type v) where
  function : α → β
  name : String
```
```lean
def succ : NamedFun Nat Nat where
  function n := n + 1
  name := "succ"

def asString [ToString α] : NamedFun α String where
  function := ToString.toString
  name := "asString"

def append : NamedFun (List α) (List α → List α) where
  function := (· ++ ·)
  name := "append"
```
```lean
def NamedFun.comp
    (f : NamedFun β γ)
    (g : NamedFun α β) :
    NamedFun α γ where
  function := f.function ∘ g.function
  name := f.name ++ " ∘ " ++ g.name
```
```lean
instance : ToString (NamedFun α α'') where
  toString f := s!"#<{f.name}>"
```
```lean (name := compDemo)
#eval asString.comp succ
```
```leanOutput compDemo
#<asString ∘ succ>
```
```leanOutput compDemo
#<asString ∘ succ>
```
```lean
instance : CoeFun (NamedFun α α'') (fun _ => α → α'') where
  coe | ⟨f, _⟩ => f
```
```lean (name := appendDemo)
#eval append [1, 2, 3] [4, 5, 6]
```
```leanOutput appendDemo
[1, 2, 3, 4, 5, 6]
```
```leanOutput appendDemo
[1, 2, 3, 4, 5, 6]
```
```lean -show
end
```
```lean
structure Writer where
  Writes : Type u
  write : Writes → String → String

def natWriter : Writer where
  Writes := Nat
  write n out := out ++ toString n

def stringWriter : Writer where
  Writes := String
  write s out := out ++ s
```
```lean
instance :
    CoeFun Writer (·.Writes → String → String) where
  coe w := w.write
```
```lean (name := writeTwice)
#eval "" |> natWriter (5 : Nat) |> stringWriter " hello"
```
```leanOutput writeTwice
"5 hello"
```
```leanOutput writeTwice
"5 hello"
```
```lean
inductive Ty where
  | nat
  | arr (dom cod : Ty)

abbrev Ty.interp : Ty → Type
  | .nat => Nat
  | .arr t t' => t.interp → t'.interp
```
```lean
inductive Tm : List Ty → Ty → Type where
  | zero : Tm Γ .nat
  | succ (n : Tm Γ .nat) : Tm Γ .nat
  | rep (n : Tm Γ .nat)
    (start : Tm Γ t)
    (f : Tm Γ (.arr .nat (.arr t t))) :
    Tm Γ t
  | lam (body : Tm (t :: Γ) t') : Tm Γ (.arr t t')
  | app (f : Tm Γ (.arr t t')) (arg : Tm Γ t) : Tm Γ t'
  | var (i : Fin Γ.length) : Tm Γ Γ[i]
deriving Repr
```
```lean
def Tm.v
    (i : Fin (Γ.length + 1)) :
    Tm (t :: Γ) (t :: Γ)[i] :=
  .var (Γ := t :: Γ) i
```
```lean
def plus : Tm [] (.arr .nat (.arr .nat .nat)) :=
  .lam <| .lam <| .rep (.v 1) (.v 0) (.lam (.lam (.succ (.v 0))))
```
```lean
def Env : List Ty → Type
  | [] => Unit
  | t :: Γ => t.interp × Env Γ

def Env.empty : Env [] := ()

def Env.extend (ρ : Env Γ) (v : t.interp) : Env (t :: Γ) :=
  (v, ρ)

def Env.get (i : Fin Γ.length) (ρ : Env Γ) : Γ[i].interp :=
  match Γ, ρ, i with
  | _::_, (v, _), ⟨0, _⟩ => v
  | _::_, (_, ρ'), ⟨i+1, _⟩ => ρ'.get ⟨i, by simp_all⟩
```
```lean
def Tm.interp (ρ : Env α'') : Tm α'' t → t.interp
  | .zero => 0
  | .succ n => n.interp ρ + 1
  | .rep n start f =>
    let f' := f.interp ρ
    (n.interp ρ).fold (fun n _ x => f' n x) (start.interp ρ)
  | .lam body => fun x => body.interp (ρ.extend x)
  | .app f arg => f.interp ρ (arg.interp ρ)
  | .var i => ρ.get i
```
```lean
instance : CoeFun (Tm [] α'') (fun _ => α''.interp) where
  coe f := f.interp .empty
```
```lean (name := evalPlus)
#eval plus
```
```leanOutput evalPlus
Tm.lam (Tm.lam (Tm.rep (Tm.var 1) (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0))))))
```
```leanOutput evalPlus
Tm.lam (Tm.lam (Tm.rep (Tm.var 1) (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0))))))
```
```lean (name := eight)
#eval plus 3 5
```
```leanOutput eight
8
```
```leanOutput eight
8
```