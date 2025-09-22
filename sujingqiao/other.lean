```lean -show
universe u
```
```lean
axiom false_is_true : False

theorem two_eq_five : 2 = 5 := false_is_true.elim
```
```lean
axiom List.free_theorem {α β}
  (f : {α : _} → List α → List α) (g : α → β) :
  f ∘ (List.map g) = (List.map g) ∘ f
```
```lean
open Classical in
noncomputable def nonParametric
    {α : _} (xs : List α) :
    List α :=
  if α = Nat then [] else xs
```
```lean
theorem unit_not_nat : Unit ≠ Nat := by
  intro eq
  have ⟨allEq⟩ := eq ▸ inferInstanceAs (Subsingleton Unit)
  specialize allEq 0 1
  contradiction

example : False := by
  have := List.free_theorem nonParametric (fun () => 42)

  unfold nonParametric at this
  simp [unit_not_nat] at this

  have := congrFun this [()]
  contradiction
```
```lean (name := otherZero)
axiom Nat.otherZero : Nat

#reduce 4 + (Nat.otherZero + 2)
```
```leanOutput otherZero
((Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) Nat.otherZero).1 4).succ.succ
```
```leanOutput otherZero
((Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) Nat.otherZero).1 4).succ.succ
```
```lean (name := otherZero2) +error
axiom Nat.otherZero : Nat

def List.length' : List α → Nat
  | [] => Nat.otherZero
  | _ :: _ => xs.length
```
```leanOutput otherZero2
`Nat.otherZero` not supported by code generator; consider marking definition as `noncomputable`
```
```leanOutput otherZero2
`Nat.otherZero` not supported by code generator; consider marking definition as `noncomputable`
```
```lean
def nextOdd (k : Nat) :
    { n : Nat // n % 2 = 1 ∧ (n = k ∨ n = k + 1) } where
  val := if k % 2 = 1 then k else k + 1
  property := by
    by_cases k % 2 = 1 <;>
    simp [*] <;> omega
```
```lean (name:=printAxNextOdd)
#print axioms nextOdd
```
```leanOutput printAxNextOdd
'nextOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```leanOutput printAxNextOdd
'nextOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```lean (name := evalNextOdd)
#eval (nextOdd 4, nextOdd 5)
```
```leanOutput evalNextOdd
(5, 5)
```
```leanOutput evalNextOdd
(5, 5)
```
```lean -show
axiom Anything : Type
``````lean
def f (n : Nat) : String :=
  if h1 : n < 11 then
    "Small"
  else if h2 : n > 13 then
    "Large"
  else if h3 : n % 2 = 1 then
    "Odd"
  else if h4 : n ≠ 12 then
    False.elim (by omega)
  else "Twelve"
```
```lean
def g (n : Nat) : String :=
  if n < 11 then
    "Small"
  else if n > 13 then
    "Large"
  else if n % 2 = 1 then
    "Odd"
  else if n ≠ 12 then
    g (n + 1)
  else "Twelve"
termination_by n
```
```lean -show
section
variable {P : Prop}
```
```lean -show
end
```
```lean -show
section
variable {A B : Prop}
```
```lean
theorem truth_functional_imp {A B : Prop} :
    ((¬ A) ∨ B) = (A → B) := by
  apply propext
  constructor
  . rintro (h | h) a <;> trivial
  . intro h
    by_cases A
    . apply Or.inr; solve_by_elim
    . apply Or.inl; trivial
```
```lean -show
end
```
```lean
theorem ex_four_plus_five : ∃ n, 4 + 5 = n := by
  exists 9
```
```lean
theorem ex_four_plus_five' : ∃ n, 4 + 5 = n := by
  constructor
  rfl
```
```lean
theorem Eq.unique {α : Sort u}
    (x y : α)
    (p1 p2 : x = y) :
    p1 = p2 := by
  rfl
```
```lean
def K {α : Sort u}
    {motive : {x : α} → x = x → Sort v}
    (d : {x : α} → motive (Eq.refl x))
    (x : α) (z : x = x) :
    motive z :=
  d

example {α : Sort u} {a : α}
    {motive : {x : α} → x = x → Sort u}
    {d : {x : α} → motive (Eq.refl x)}
    {v : motive (Eq.refl a)} :
    K (motive := motive) d a rfl = d := by
  rfl
```
```lean -show
section
variable (x : α) (y : β)
```
```lean -show
end
```
```lean -show
variable {α : Type u} {n k l₁ l₂ l₃ : Nat}
```
```lean
variable
  {xs : Vector α l₁} {ys : Vector α l₂} {zs : Vector α l₃}
set_option linter.unusedVariables false
```
```lean (name := assocFail) +error -keep
theorem Vector.append_associative :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by sorry
```
```leanOutput assocFail
Type mismatch
  xs ++ ys ++ zs
has type
  Vector α (l₁ + l₂ + l₃)
but is expected to have type
  Vector α (l₁ + (l₂ + l₃))
```
```leanOutput assocFail
Type mismatch
  xs ++ ys ++ zs
has type
  Vector α (l₁ + l₂ + l₃)
but is expected to have type
  Vector α (l₁ + (l₂ + l₃))
```
```lean
theorem Vector.append_associative' :
    xs ++ (ys ++ zs) =
    Nat.add_assoc _ _ _ ▸ ((xs ++ ys) ++ zs) := by
  sorry
```
```lean -keep
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by sorry
```
```lean -keep
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by
  cases xs; cases ys; cases zs
  simp
  congr 1
  . omega
  . apply heq_of_eqRec_eq
    . rfl
    . apply propext
      constructor <;> intro h <;> simp_all +arith
``````lean -show
variable {m : Type → Type} [Monad m] {α : Type}
```
```lean
example (e1 e2 : Unit) : e1 = e2 := rfl
```
```lean
inductive CustomUnit where
  | customUnit

example (e1 e2 : CustomUnit) : e1 = e2 := rfl

structure AlsoUnit where

example (e1 e2 : AlsoUnit) : e1 = e2 := rfl
```
```lean
inductive WithParam (n : Nat) where
  | mk

example (x y : WithParam 3) : x = y := rfl
```
```lean
inductive NotUnitLike where
  | mk (u : Unit)
```
```lean +error (name := NotUnitLike)
example (e1 e2 : NotUnitLike) : e1 = e2 := rfl
```
```leanOutput NotUnitLike
Type mismatch
  rfl
has type
  ?m.13 = ?m.13
but is expected to have type
  e1 = e2
```
```leanOutput NotUnitLike
Type mismatch
  rfl
has type
  ?m.13 = ?m.13
but is expected to have type
  e1 = e2
```
```lean
inductive ProofUnitLike where
  | mk : 2 = 2 → ProofUnitLike

example (e1 e2 : ProofUnitLike) : e1 = e2 := rfl
```
```lean -show
section BoolProp

axiom b : Bool

/-- info: b = true : Prop -/
#check_msgs in
#check (b : Prop)

example : (true = true) = True := by simp

#check decide
```
```lean -show
/-- info: true -/
#check_msgs in
#eval (2 = 2 : Bool)
end BoolProp
```
```lean -show
section ShortCircuit

axiom BIG_EXPENSIVE_COMPUTATION : Bool
```
```lean -show
end ShortCircuit
``````lean
def add (n : Nat) : (k : Nat) → Nat
  | 0 => n
  | k' + 1 => 1 + add n k'
```
```lean
def mustBeEqual (n : Nat) : (k : Nat) → n = k → String :=
  fun _ =>
    fun
    | rfl => s!"Equal - both are {n}!"

```
```lean -show
variable {α : Type u} {β : Type v}
```
```lean
def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```lean -show
universe u v
variable {α : Type u} {β : Type v}
```
```lean +error (name := noAuto)
set_option autoImplicit false

def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput noAuto
Unknown identifier `α`
```
```leanOutput noAuto
Unknown identifier `α`
```
```leanOutput noAuto
Unknown identifier `β`
```
```leanOutput noAuto
Unknown identifier `β`
```
```lean -keep
set_option autoImplicit false

def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```lean -keep
set_option autoImplicit false

def map {α β} (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```lean -show
variable (i : Fin n)
```
```lean
structure AtLeast (i : Fin n) where
  val : Nat
  val_gt_i : val ≥ i.val
```
```lean
def AtLeast.add (x y : AtLeast i) : AtLeast i :=
  AtLeast.mk (x.val + y.val) <| by
    cases x
    cases y
    dsimp only
    omega
```
```lean -show
variable (i : Fin n)
```
```lean (name := checkAdd)
#check AtLeast.add
```
```leanOutput checkAdd
AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
```
```leanOutput checkAdd
AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
```
```lean
inductive Answer where
  | yes
  | maybe
  | no
```
```lean  (name := asnwer) +error
def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput asnwer
Invalid dotted identifier notation: The expected type of `.yes`
  Asnwer
is not of the form `C ...` or `... → C ...` where C is a constant
```
```leanOutput asnwer
Invalid dotted identifier notation: The expected type of `.yes`
  Asnwer
is not of the form `C ...` or `... → C ...` where C is a constant
```
```lean  (name := asnwer2) +error
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput asnwer2
Unknown identifier `Asnwer`
```
```leanOutput asnwer2
Unknown identifier `Asnwer`
```
```lean
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```lean +error (name := noauto)
set_option autoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput noauto
Unknown identifier `α`
```
```leanOutput noauto
Unknown identifier `α`
``````lean -show
open Lean.Elab (Info)
```
```lean -show -keep
-- Test definitional eta for structures
structure A where
  x : Nat
  y : Int
example (a : A) : ⟨a.x, a.y⟩ = a := rfl
set_option linter.unusedVariables false in
inductive B where
  | mk (x : Nat) (y : Int) : B
example (b : B) : ⟨b.1, b.2⟩ = b := rfl
/--
error: Type mismatch
  rfl
has type
  ?m.836 = ?m.836
but is expected to have type
  e1 = e2
-/
#check_msgs in
example (e1 e2 : Empty) : e1 = e2 := rfl
```
```lean -show -keep
def third_of_five : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
set_option pp.match false
/--
info: third_of_five.eq_def.{u_1} {α : Type u_1} (x✝ : List α) :
  third_of_five x✝ = third_of_five.match_1 (fun x => Option α) x✝ (fun head head x head head => some x) fun x => none
-/
#check_msgs in
#check third_of_five.eq_def
/--
info: def third_of_five.match_1.{u_1, u_2} : {α : Type u_1} →
  (motive : List α → Sort u_2) →
    (x : List α) →
      ((head head_1 x head_2 head_3 : α) → motive [head, head_1, x, head_2, head_3]) →
        ((x : List α) → motive x) → motive x :=
fun {α} motive x h_1 h_2 =>
  List.casesOn x (h_2 []) fun head tail =>
    List.casesOn tail (h_2 [head]) fun head_1 tail =>
      List.casesOn tail (h_2 [head, head_1]) fun head_2 tail =>
        List.casesOn tail (h_2 [head, head_1, head_2]) fun head_3 tail =>
          List.casesOn tail (h_2 [head, head_1, head_2, head_3]) fun head_4 tail =>
            List.casesOn tail (h_1 head head_1 head_2 head_3 head_4) fun head_5 tail =>
              h_2 (head :: head_1 :: head_2 :: head_3 :: head_4 :: head_5 :: tail)
-/
#check_msgs in
#print third_of_five.match_1
```
```lean
def thirdOfFive : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
```
```lean
def everyOther : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: everyOther xs
``````lean -show
-- Open some namespaces for the examples.
open Lean Lean.Grind Lean.Meta.Grind
```
```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  grind
```
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```
```lean
example (x y : Fin 11) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
```lean
example (x y : Int) :
    27 ≤ 11 * x + 13 * y →
    11 * x + 13 * y ≤ 45 →
    -10 ≤ 7 * x - 9 * y →
    7 * x - 9 * y ≤ 4 →
    False := by
  grind
``````lean
def hello : IO Unit := IO.println "Hello, world!"
```
```lean (name := output) +error
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ "two"
```
```leanOutput output (severity := information)
"The answer is 4"
```
```leanOutput output (severity := information)
"The answer is 4"
```
```leanOutput output (severity := warning)
declaration uses 'sorry'
```
```leanOutput output (severity := warning)
declaration uses 'sorry'
```
```leanOutput output (severity := error)
Application type mismatch: The argument
  "two"
has type
  String
but is expected to have type
  Nat
in the application
  Nat.succ "two"
```
```leanOutput output (severity := error)
Application type mismatch: The argument
  "two"
has type
  String
but is expected to have type
  Nat
in the application
  Nat.succ "two"
```
```lean
example : 2 + 2 = 4 := by rfl
```
```leanOutput intro
<example>:3:3-3:6: unexpected token '=>'; expected term
```
```leanOutput intro
<example>:3:3-3:6: unexpected token '=>'; expected term
```
```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)
```
```lean
/--
Evenness: a number is even if it can be evenly divided by two.
-/
inductive Even : Nat → Prop where
  | /-- 0 is considered even here -/
    zero : Even 0
  | /-- If `n` is even, then so is `n + 2`. -/
    plusTwo : Even n → Even (n + 2)
``````lean -show
-- Validate the above description of reducibility

@[irreducible]
def foo (x : α) := x

set_option allowUnsafeReducibility true in
@[semireducible]
def foo' (x : α) := x

@[reducible]
def foo'' (x : α) := x

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo (x, y) = (y, x) := by
  simp [foo]

/-- error: `simp` made no progress -/
#check_msgs in
example : foo (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo' (x, y) = (y, x) := by
  simp [foo']

/-- error: `simp` made no progress -/
#check_msgs in
example : foo' (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo'' (x, y) = (y, x) := by
  simp [foo'']

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo'' (x, y) = (y, x) := by
  simp

```
```lean -show
-- Check above claim about default priority
/-- info: 1000 -/
#check_msgs in
#eval eval_prio default
```
```lean (name:=simpHuhDemo)
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp?
  assumption
```
```leanOutput simpHuhDemo
Try this:
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
```
```leanOutput simpHuhDemo
Try this:
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
```
```lean
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
  assumption
``````lean -show
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#check_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#check_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "αποδεικνύοντας"

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#check_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Success! Final stack:\n  `øvelse\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "øvelse"

/-- info: "Success! Final stack:\n  `Übersetzung\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "Übersetzung"

/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#check_msgs in
#eval validIdentifier "переклад"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"汉语\"" -/
#check_msgs in
#eval validIdentifier "汉语"


```
```lean -show
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "««one line\nand another»"

/-- info: "Success! Final stack:\n  `«one line\x00and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x00and another»"

/-- info: "Success! Final stack:\n  `«one line\x0band another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x0Band another»"
``````lean -show
axiom α : Type
axiom x : α
axiom xs : List α
axiom ih : xs ++ [] = xs
```
```lean -show
variable (n : Nat)
```
```lean
example : x < 3 → x ∈ [0, 1, 2] := by
  intros
  iterate 3
    cases ‹Nat›
    . decide
  contradiction
```
```lean (name := evalGuillemets)
#eval
  let x := 1
  let y := 2
  ‹Nat›
```
```leanOutput evalGuillemets
2
```
```leanOutput evalGuillemets
2
```
```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  if n = 0 then
    simp [*]
  else
    simp only [↓reduceIte, gt_iff_lt, *]
    omega
```
```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  match n with
  | 0 =>
    simp
  | k + 1 =>
    simp
```